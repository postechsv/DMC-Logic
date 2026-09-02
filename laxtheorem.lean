import Mathlib.Logic.Basic

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
