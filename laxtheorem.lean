import Mathlib.Logic.Basic
import Lean.Elab.Tactic

/-!
# A lax modality for speculative proofs

`Lax α` packages a condition together with a value of `α` that can be
obtained once that condition is certified.  `PSigma` is used rather than
`Sigma` so that `α` may be a proposition as well as a type.
-/

universe u v

/-- A speculative value of `α`, guarded by an internal proposition. -/
abbrev Lax (α : Sort u) :=
  PSigma (fun P : Prop => P → α)

/-- Notation for the lax modality. -/
prefix:100 "◯" => Lax

namespace Lax

/-- `condition : ◯α → Prop`. -/
def condition {α : Sort u} (s : ◯α) : Prop :=
  s.fst

/-- `certify : (s : ◯α) → s.condition → α` (`◯`-elimination). -/
def certify {α : Sort u} (s : ◯α) (h : s.condition) : α :=
  s.snd h

/-- `ret : α → ◯α`. -/
def ret {α : Sort u} (a : α) : ◯α :=
  ⟨True, fun _ => a⟩

/-- `bind : ◯α → (α → ◯β) → ◯β`. -/
def bind {α : Sort u} {β : Sort v} (s : ◯α) (k : α → ◯β) : ◯β :=
  ⟨∃ h : s.condition, (k (s.certify h)).condition,
    fun h => (k (s.certify h.1)).certify h.2⟩

/-- `mult : ◯◯α → ◯α`. -/
def mult {α : Sort u} (s : ◯◯α) : ◯α :=
  bind s id

/-- `mono : (α → β) → (◯α → ◯β)`. -/
def mono {α : Sort u} {β : Sort v} (f : α → β) (s : ◯α) : ◯β :=
  bind s fun a => ret (f a)

/-- `strength : ◯P → ◯Q → ◯(P ∧ Q)`. -/
def strength {P Q : Prop} (s : ◯P) (t : ◯Q) : ◯(P ∧ Q) :=
  bind s fun p =>
    bind t fun q =>
      ret ⟨p, q⟩

/-- `assume P : ◯P` for every `P : Prop`. -/
def «assume» (P : Prop) : ◯P :=
  ⟨P, id⟩

end Lax

/-- One binding in `lax do` notation. -/
declare_syntax_cat laxDoBind
syntax ident " ← " term ";" : laxDoBind

/--
`lax do` notation for sequencing lax proofs.  A block

```lean
lax do
  x ← mx;
  y ← my x;
  return result x y
```

expands to nested applications of `Lax.bind`, with `Lax.ret` around the
returned value.  Unlike ordinary `do`, this notation also supports payloads
in `Prop`.
-/
syntax:lead "lax" " do " laxDoBind* "return " term : term

macro_rules
  | `(lax do $[$binds:laxDoBind]* return $result:term) => do
      let mut expansion ← `(Lax.ret $result)
      for bind in binds.reverse do
        match bind with
        | `(laxDoBind| $x:ident ← $action:term;) =>
          expansion ← `(Lax.bind $action fun $x => $expansion)
        | _ => pure ()
      return expansion






namespace UnifExample

open Lax



/-
Why unification is a good motivating example for "proof modulo certification":
- per-instance
  the correctness of unification tactic itself is not need as proof obligation.
  only the per-instance correctness (which is completeness of unifiers) is sufficient.
- efficient heuristic
  although unification is in general intractable, it can be solved efficiently in practice;
  the main proof check could enjoy this when certification is deferred via modularity.
- large certification
  even the per-instance correctness might be non-trivial certification,
  justifying practical need for decomposing certification from main proof.
- a posteriori certification
  certification obligation is only known after calling unification tactic;
  usual lemmas cannot be used for decomposition as they need to be stated statically.
-/


/-
Let's say we want to prove GOAL,
assuming two terms t1 and t2 are equal (modulo some axioms e.g., ACU):
  main theorem: T1_EQ_T2 → GOAL
where T1_EQ_T2 stands for a unification problem of two terms t1 and t2.

In proving the main theorem, we might need completeness of the unifiers
  completeness: T1_EQ_T2 → MGU1 ∨ MGU2 ∨ MGU3
which is not known a priori before stating the main theorem.

Hence, the proof of main theorem would morally look like
  theorem: T1_EQ_T2 → GOAL
  proof:
  1) assume (T1_EQ_T2 → MGU1 ∨ MGU2 ∨ MGU3) -- this prop is dynamically generated
  2) apply the assumption to get MGU1 ∨ MGU2 ∨ MGU3
  3) · prove MGU1 → GOAL
     · prove MGU2 → GOAL
     · prove MGU3 → GOAL

Clearly, this proof has a certification hole (i.e., step 1).
Using our Lax modality
  theorem: ◯(T1_EQ_T2 → GOAL)

-/



-- main theorem: T1_EQ_T2 → GOAL
axiom T1_EQ_T2 : Prop
axiom GOAL : Prop

axiom MGU1 : Prop
axiom MGU2 : Prop
axiom MGU3 : Prop

axiom easy_proof1 : MGU1 → GOAL
axiom easy_proof2 : MGU2 → GOAL
axiom easy_proof3 : MGU3 → GOAL

axiom completeness_pf : T1_EQ_T2 → MGU1 ∨ MGU2 ∨ MGU3

open Lean Elab Tactic Meta

/--
Stand-in for the dynamic unification generator.  A real implementation would
compute the alternatives instead of referring to the three example MGUs.
-/
private def generate_unification_obligation (problem : Expr) : MetaM Expr := do
  let alternatives := mkApp2 (mkConst ``Or) (mkConst ``MGU1)
    (mkApp2 (mkConst ``Or) (mkConst ``MGU2) (mkConst ``MGU3))
  return mkForall Name.anonymous BinderInfo.default problem alternatives

/--
Generate a unification obligation, insert it into the current lax proof via
`mono`, and expose it as a normal local hypothesis.
-/
syntax "lax_unify " term " as " ident : tactic

elab_rules : tactic
  | `(tactic| lax_unify $problemStx:term as $h:ident) => do
      let problem ← elabTermEnsuringType problemStx (mkSort .zero)
      let obligation ← generate_unification_obligation problem
      let obligationStx ← Term.exprToSyntax obligation
      evalTactic (← `(tactic|
        refine Lax.mono (α := $obligationStx) ?_ (Lax.assume $obligationStx) <;>
          intro $h:ident))


-- The generated completeness type is absent from both the signature and proof source.
def lax_main_dynamic : ◯(T1_EQ_T2 → GOAL) := by
  lax_unify T1_EQ_T2 as cert_hole
  intro hEq
  rcases cert_hole hEq with h1 | h2 | h3
  · exact easy_proof1 h1
  · exact easy_proof2 h2
  · exact easy_proof3 h3

set_option pp.proofs true in
#reduce UnifExample.lax_main_dynamic
-- TODO: reduce _proof1_ & _proof2_


-- MGU's appear explicitly only for illustrative purpose
def unif_tactic (T1_EQ_T2 : Prop) : ◯(T1_EQ_T2 → MGU1 ∨ MGU2 ∨ MGU3)
  := assume (T1_EQ_T2 → MGU1 ∨ MGU2 ∨ MGU3) -- generated dynamically



/- STEP 1 : finish the proof modulo certification -/
-- cert_hole = proof obligation
def lax_main : ◯(T1_EQ_T2 → GOAL) :=
  bind (unif_tactic T1_EQ_T2) fun cert_hole =>
    ret fun hEq =>
      match cert_hole hEq with
      | Or.inl h1 => easy_proof1 h1
      | Or.inr (Or.inl h2) => easy_proof2 h2
      | Or.inr (Or.inr h3) => easy_proof3 h3

-- The same monadic proof using imperative-style notation.
def lax_main' : ◯(T1_EQ_T2 → GOAL) := lax do
  cert_hole ← unif_tactic T1_EQ_T2;
  return by
    intro hEq
    rcases cert_hole hEq with h1 | h2 | h3
    · exact easy_proof1 h1
    · exact easy_proof2 h2
    · exact easy_proof3 h3





/- STEP 2 : fill in the certification hole -/
theorem main : T1_EQ_T2 → GOAL :=
  (lax_main).certify ⟨completeness_pf, trivial⟩


/-
Our decomposition: MGUs appears only implicitly
  (main proof) T1_EQ_T2 (→ MGU1 ∨ MGU2 ∨ MGU3) → GOAL
  (certification) T1_EQ_T2 → GOAL
=> automatic unification is a LOCAL proof tactic
=> encapsulation

Traditional decomposition: MGUS appears explicitly
  (certification) T1_EQ_T2 → MGU1 ∨ MGU2 ∨ MGU3
  (main proof) theorem T1_EQ_T2 → GOAL
=> automatic unification is a GLOBAL meta-programming
=> i.e., modifies the global codebase

Monolithic (= using `sorry`):
  (main proof & certification) T1_EQ_T2 → GOAL
=> nothing can be justified unless proof is complete
=> tactic could be used locally, but less modular

Our lax typing allows COMPOSITIONALITY & ENCAPSULATION

TODO: main explicit example for traditional workflow
-/


end UnifExample


namespace LaxMonadExamples

open Lax

/-!
## Monadic reading

For a functional programmer, `◯α` is a computation that returns an `α` once
its logical effect has been discharged.  A value `s : ◯α` contains both an
effect `s.condition : Prop` and a continuation
`s.certify : s.condition → α`.

* `ret a` is the pure computation.  Its condition is `True`.
* `bind s k` sequences two computations.  Its condition is
  `∃ h : s.condition, (k (s.certify h)).condition`.
* `mono` is `map`, defined by sequencing followed by `ret`.
* `mult` is monadic `join`.
* `strength` is applicative pairing of two independent computations.
* `assume P` is the effect operation that requests a proof of `P` and then
  returns that proof.

The existential in `bind` is the important part: the condition generated by
the continuation may depend on the value produced by the first computation.
Thus this is not merely a writer that accumulates a flat conjunction.  A
later obligation can depend on generated data, and different data constructors
can select different later obligations.

The raw `PSigma` representation is monad-shaped rather than a Lean `Monad`
instance: it accepts payloads in any `Sort`, including `Prop`, and its laws
identify logically equivalent conditions rather than reducing by `rfl`.

Lean also prevents eliminating arbitrary proofs in `Prop` to choose data in
`Type`.  Therefore the dependent examples below let generators return data in
`Type`, guarded by propositions.  Plain `lax_assume P` remains appropriate
when the generated result is only the proof `P`.

The proof commands below are direct tactic-mode presentations of ordinary
monadic notation:

```text
lax_bind mx as x       ≈ bind mx (fun x => ...)
lax_assume P as h      ≈ bind (assume P) (fun h => ...)
lax_return; proof      ≈ ret (by proof)
```

`lax_intro` is not a monad operation.  It uses `pi` to move a dependent
function space through `◯`, allowing the usual introduction-and-reasoning
style while subsequent monadic effects remain possible.
-/

/-- Sequence an arbitrary lax computation and name its generated value. -/
syntax "lax_bind " term " as " ident : tactic

macro_rules
  | `(tactic| lax_bind $action:term as $x:ident) =>
      `(tactic|
        refine Lax.bind $action ?_ <;>
          intro $x:ident)

/-- Introduce a generated assumption while keeping the remaining goal lax. -/
syntax "lax_assume " term " as " ident : tactic

macro_rules
  | `(tactic| lax_assume $P:term as $h:ident) =>
      `(tactic|
        refine Lax.bind (Lax.assume $P) ?_ <;>
          intro $h:ident)

/-- Finish generating assumptions and return to an ordinary Lean proof goal. -/
syntax "lax_return" : tactic

macro_rules
  | `(tactic| lax_return) => `(tactic| refine Lax.ret ?_)

/-- Move a dependent function constructor through the lax modality. -/
def pi {α : Sort u} {β : α → Sort v} (f : (a : α) → ◯(β a)) : ◯((a : α) → β a) :=
  ⟨∀ a, (f a).condition, fun h a => (f a).certify (h a)⟩

/-- Introduce an ordinary argument without leaving lax proof mode. -/
syntax "lax_intro " ident : tactic

macro_rules
  | `(tactic| lax_intro $a:ident) =>
      `(tactic|
        refine pi ?_ <;>
          intro $a:ident)


/- ## 1. Sequentially composing generated assumptions -/

axiom Candidate : Nat → Prop
axiom Valid : Nat → Prop
axiom SequentialGoal : Prop

axiom generatedCandidate : Nat

/-- A generated candidate together with a deferred proof that it is valid output. -/
noncomputable def generateCandidate : ◯{n // Candidate n} :=
  ⟨Candidate generatedCandidate, fun h => ⟨generatedCandidate, h⟩⟩

axiom finishSequential :
  ∀ n, Candidate n → Valid n → SequentialGoal

/-- The second generated assumption depends on the witness produced by the first. -/
noncomputable def sequential : ◯SequentialGoal := by
  lax_bind generateCandidate as candidate
  lax_assume (Valid candidate.val) as hvalid
  lax_return
  exact finishSequential candidate.val candidate.property hvalid


/- ## 2. Alternating ordinary proof steps and generated assumptions -/

axiom Input : Prop
axiom FirstCertificate : Prop
axiom DerivedFact : Prop
axiom SecondCertificate : Prop
axiom CombinedFact : Prop
axiom AlternatingGoal : Prop

axiom deriveFact : Input → FirstCertificate → DerivedFact
axiom combineFacts : DerivedFact → SecondCertificate → CombinedFact
axiom finishAlternating : CombinedFact → AlternatingGoal

/-- Ordinary `have` proofs can be interleaved with effectful assumption generation. -/
def alternating : ◯(Input → AlternatingGoal) := by
  lax_intro hInput
  lax_assume FirstCertificate as hFirst

  have hDerived : DerivedFact := by
    exact deriveFact hInput hFirst

  lax_assume SecondCertificate as hSecond

  have hCombined : CombinedFact := by
    exact combineFacts hDerived hSecond

  lax_return
  exact finishAlternating hCombined


/- ## 3. Nested, branch-dependent assumptions -/

axiom BranchCandidate : Type
axiom LeftCase : BranchCandidate → Prop
axiom RightCase : BranchCandidate → Prop
axiom LeftRequirement : BranchCandidate → Prop
axiom RightRequirement : BranchCandidate → Prop
axiom NestedGoal : Prop

axiom generatedBranch : Sum BranchCandidate BranchCandidate

def BranchSound : Sum BranchCandidate BranchCandidate → Prop
  | Sum.inl candidate => LeftCase candidate
  | Sum.inr candidate => RightCase candidate

/-- A generated branch whose branch-selection proof is deferred. -/
noncomputable def generateBranch : ◯{branch // BranchSound branch} :=
  ⟨BranchSound generatedBranch, fun h => ⟨generatedBranch, h⟩⟩

axiom solveLeft :
  ∀ candidate, LeftCase candidate → LeftRequirement candidate → NestedGoal

axiom solveRight :
  ∀ candidate, RightCase candidate → RightRequirement candidate → NestedGoal

/-- Only the additional assumption belonging to the selected branch is generated. -/
noncomputable def nested : ◯NestedGoal := by
  lax_bind generateBranch as branch
  rcases branch with ⟨candidate | candidate, hcase⟩
  · lax_assume (LeftRequirement candidate) as hrequired
    lax_return
    exact solveLeft candidate hcase hrequired
  · lax_assume (RightRequirement candidate) as hrequired
    lax_return
    exact solveRight candidate hcase hrequired

end LaxMonadExamples


namespace FiniteGraphExample

open Lax

/-!
## Model checking a finite graph

The reachable graph rooted at `s0` has depth three:

```text
s0
├── s1
│   └── s3
│       └── s6
└── s2
    ├── s4
    │   └── s7
    └── s5
        └── s8

s9 is unsafe but unreachable.
```
-/

inductive State where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9
  deriving DecidableEq, Repr

open State

/-- The actual transition relation of the model. -/
inductive Step : State → State → Prop where
  | step01 : Step s0 s1
  | step02 : Step s0 s2
  | step13 : Step s1 s3
  | step24 : Step s2 s4
  | step25 : Step s2 s5
  | step36 : Step s3 s6
  | step47 : Step s4 s7
  | step58 : Step s5 s8

/-- Successor lists computed by the model checker. -/
def next : State → List State
  | s0 => [s1, s2]
  | s1 => [s3]
  | s2 => [s4, s5]
  | s3 => [s6]
  | s4 => [s7]
  | s5 => [s8]
  | s6 | s7 | s8 | s9 => []

/-- Safety itself is an ordinary proposition, not a lax proposition. -/
axiom isSafe : State → Prop

axiom safeS0 : isSafe s0
axiom safeS1 : isSafe s1
axiom safeS2 : isSafe s2
axiom safeS3 : isSafe s3
axiom safeS4 : isSafe s4
axiom safeS5 : isSafe s5
axiom safeS6 : isSafe s6
axiom safeS7 : isSafe s7
axiom safeS8 : isSafe s8
axiom unsafeS9 : ¬isSafe s9

/-- Reachability follows zero or more edges, starting at the first argument. -/
inductive Reachable : State → State → Prop where
  | refl (state) : Reachable state state
  | step {source middle target} :
      Step source middle → Reachable middle target → Reachable source target

/-- Every state reachable from `source`, including `source`, is safe. -/
def SafeFrom (source : State) : Prop :=
  ∀ target, Reachable source target → isSafe target

/--
Local safety and exhaustive computed children suffice for global safety from
the current state.  The predicate `computedChild` uniformly covers leaves,
unary nodes, and branching nodes.
-/
theorem allSafe_of_children {source : State} {computedChild : State → Prop}
    (safeHere : isSafe source)
    (complete : ∀ child, Step source child → computedChild child)
    (safeChildren : ∀ child, computedChild child → SafeFrom child) :
    SafeFrom source := by
  intro target reachable
  cases reachable with
  | refl => exact safeHere
  | step edge reachable =>
      exact safeChildren _ (complete _ edge) _ reachable

/-! ### Construct the safety proof before certifying successor completeness -/

/--
The main theorem states global safety directly. Its proof bullets follow the
computed graph, while each `lax_assume` records that the displayed outgoing
edges at one state are complete.
-/
-- TODO: eliminate recursive structure due to let ... : make it truely forward
-- make it tail-recursive?
-- maybe i may modify the completeness
-- e.g. s0 -> s1, s2
-- completeness: suffices to check modelcheck s1 and modelcheck s2
-- so parameterize the modelCheck by state
-- TODO: what if it is general directed graph rather than tree?
def modelCheck : ◯(SafeFrom s0) := by
  have currentSafe : isSafe s0 := safeS0
  lax_assume (∀ target, Step s0 target → target = s1 ∨ target = s2) as completeHere

  refine Lax.mono (α := SafeFrom s1 ∧ SafeFrom s2) (by
    rintro ⟨safeFromS1, safeFromS2⟩
    apply allSafe_of_children currentSafe completeHere
    intro child generated
    rcases generated with rfl | rfl
    · exact safeFromS1
    · exact safeFromS2) (Lax.strength ?_ ?_)

  · -- s1
    have currentSafe : isSafe s1 := safeS1
    lax_assume (∀ target, Step s1 target → target = s3) as completeHere

    refine Lax.mono (α := SafeFrom s3) (by
      intro safeFromS3
      apply allSafe_of_children currentSafe completeHere
      intro child generated
      rw [generated]
      exact safeFromS3) ?_

    · -- s3
      have currentSafe : isSafe s3 := safeS3
      lax_assume (∀ target, Step s3 target → target = s6) as completeHere

      refine Lax.mono (α := SafeFrom s6) (by
        intro safeFromS6
        apply allSafe_of_children currentSafe completeHere
        intro child generated
        rw [generated]
        exact safeFromS6) ?_

      · -- s6
        have currentSafe : isSafe s6 := safeS6
        lax_assume (∀ target, Step s6 target → False) as completeHere
        lax_return
        apply allSafe_of_children currentSafe completeHere
        intro child impossible
        exact False.elim impossible

  · -- s2
    have currentSafe : isSafe s2 := safeS2
    lax_assume (∀ target, Step s2 target → target = s4 ∨ target = s5) as completeHere

    refine Lax.mono (α := SafeFrom s4 ∧ SafeFrom s5) (by
      rintro ⟨safeFromS4, safeFromS5⟩
      apply allSafe_of_children currentSafe completeHere
      intro child generated
      rcases generated with rfl | rfl
      · exact safeFromS4
      · exact safeFromS5) (Lax.strength ?_ ?_)

    · -- s4
      have currentSafe : isSafe s4 := safeS4
      lax_assume (∀ target, Step s4 target → target = s7) as completeHere

      refine Lax.mono (α := SafeFrom s7) (by
        intro safeFromS7
        apply allSafe_of_children currentSafe completeHere
        intro child generated
        rw [generated]
        exact safeFromS7) ?_

      · -- s7
        have currentSafe : isSafe s7 := safeS7
        lax_assume (∀ target, Step s7 target → False) as completeHere
        lax_return
        apply allSafe_of_children currentSafe completeHere
        intro child impossible
        exact False.elim impossible

    · -- s5
      have currentSafe : isSafe s5 := safeS5
      lax_assume (∀ target, Step s5 target → target = s8) as completeHere

      refine Lax.mono (α := SafeFrom s8) (by
        intro safeFromS8
        apply allSafe_of_children currentSafe completeHere
        intro child generated
        rw [generated]
        exact safeFromS8) ?_

      · -- s8
        have currentSafe : isSafe s8 := safeS8
        lax_assume (∀ target, Step s8 target → False) as completeHere
        lax_return
        apply allSafe_of_children currentSafe completeHere
        intro child impossible
        exact False.elim impossible


/-! ### Certify the accumulated local obligations -/

axiom completeS0 : ∀ target, Step s0 target → target = s1 ∨ target = s2
axiom completeS1 : ∀ target, Step s1 target → target = s3
axiom completeS2 : ∀ target, Step s2 target → target = s4 ∨ target = s5
axiom completeS3 : ∀ target, Step s3 target → target = s6
axiom completeS4 : ∀ target, Step s4 target → target = s7
axiom completeS5 : ∀ target, Step s5 target → target = s8
axiom completeS6 : ∀ target, Step s6 target → False
axiom completeS7 : ∀ target, Step s7 target → False
axiom completeS8 : ∀ target, Step s8 target → False

/-- The deferred conditions from every nested expansion are discharged here. -/
theorem modelCheckCondition : modelCheck.condition := by
  simp [modelCheck, Lax.bind, Lax.ret, Lax.assume, Lax.condition,
    Lax.mono, Lax.strength]
  exact ⟨completeS5,
    ⟨⟨completeS4, completeS7⟩, completeS2,
      ⟨⟨completeS3, completeS1, completeS6⟩, completeS0, completeS8⟩⟩⟩
-- TODO: prove one by one as lemmas without explicitly stating completeness prop

/-- Eliminate `◯` only after the whole model-checking proof has been built. -/
theorem certifiedModel : ∀ target, Reachable s0 target → isSafe target :=
  modelCheck.certify modelCheckCondition

/-- Final global safety theorem for every state reachable from `s0`. -/
theorem globalSafety {state : State} (reachable : Reachable s0 state) : isSafe state :=
  certifiedModel state reachable

end FiniteGraphExample
