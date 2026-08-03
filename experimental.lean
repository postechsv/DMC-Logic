import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Lean.Meta.Simp

namespace framework

universe u v w x

-- α is the type of states
class State (α : Type u) : Prop where

-- P is a type of atomic patterns denoting sets of α-states.
class AtPattern (α : Type u) [State α] (P : Type v) where
  semantics : P → α → Prop

instance {α : Type u} [State α] : AtPattern α (α × Prop) where
  semantics p state := p.fst = state ∧ p.snd

instance {α : Type u} {A : Type v} {P : Type w}
    [State α] [AtPattern α P] : AtPattern α (A → P) where
  semantics p state := ∃ x, AtPattern.semantics (p x) state

-- P is either an atomic pattern or a disjunction of patterns.
class Pattern (α : Type u) [State α] (P : Type v) where
  semantics : P → α → Prop

def Pattern.denotes
    {α : Type u} [State α] {P : Type v} [Pattern α P]
    (pattern : P) (state : α) : Prop :=
  Pattern.semantics pattern state

instance {α : Type u} {P : Type v} [State α] [AtPattern α P] :
    Pattern α P where
  semantics := AtPattern.semantics

structure Disjunction (P : Type v) (Q : Type w) where
  left : P
  right : Q

scoped[Disjunction] infixr:65 " ⊔ " => framework.Disjunction.mk

instance {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q] :
    Pattern α (Disjunction P Q) where
  semantics patterns state :=
    Pattern.semantics patterns.left state ∨
    Pattern.semantics patterns.right state

theorem Pattern.disjunction_assoc
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [Pattern α R]
    (p : P) (q : Q) (r : R) (state : α) :
    Pattern.semantics (Disjunction.mk (Disjunction.mk p q) r) state ↔
      Pattern.semantics (Disjunction.mk p (Disjunction.mk q r)) state := by
  change
    (Pattern.semantics p state ∨ Pattern.semantics q state) ∨
        Pattern.semantics r state ↔
      Pattern.semantics p state ∨
        (Pattern.semantics q state ∨ Pattern.semantics r state)
  exact or_assoc



-- R is a type of atomic rules denoting transitions between α-states.
class AtRule (α : Type u) [State α] (R : Type v) where
  semantics : R → α → α → Prop

instance {α : Type u} [State α] : AtRule α (α × α × Prop) where
  semantics r before after :=
    r.1 = before ∧ r.2.1 = after ∧ r.2.2

instance {α : Type u} {A : Type v} {R : Type w}
    [State α] [AtRule α R] : AtRule α (A → R) where
  semantics r before after := ∃ x, AtRule.semantics (r x) before after

-- R is either an atomic rule or a disjunction of rules.
class Rule (α : Type u) [State α] (R : Type v) where
  semantics : R → α → α → Prop

instance {α : Type u} {R : Type v} [State α] [AtRule α R] :
    Rule α R where
  semantics := AtRule.semantics

instance {α : Type u} {R : Type v} {S : Type w}
    [State α] [Rule α R] [Rule α S] :
    Rule α (Disjunction R S) where
  semantics rules before after :=
    Rule.semantics rules.left before after ∨
    Rule.semantics rules.right before after

theorem Rule.disjunction_assoc
    {α : Type u} {R : Type v} {S : Type w} {T : Type x}
    [State α] [Rule α R] [Rule α S] [Rule α T]
    (r : R) (s : S) (t : T) (before after : α) :
    Rule.semantics (Disjunction.mk (Disjunction.mk r s) t) before after ↔
      Rule.semantics (Disjunction.mk r (Disjunction.mk s t)) before after := by
  change
    (Rule.semantics r before after ∨ Rule.semantics s before after) ∨
        Rule.semantics t before after ↔
      Rule.semantics r before after ∨
        (Rule.semantics s before after ∨ Rule.semantics t before after)
  exact or_assoc



def postImage {α : Type u} {P : Type v} {R : Type w}
    [State α] [Pattern α P] [Rule α R]
    (r : R) (p : P) : α → Prop :=
  fun after =>
    ∃ before,
      Pattern.semantics p before ∧
      Rule.semantics r before after

def mapsInto
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [Rule α R]
    (r : R) (p : P) (target : Q) : Prop :=
  ∀ (before after : α),
    Pattern.semantics p before →
    Rule.semantics r before after →
    Pattern.semantics target after

-- An oracle result associates a unification premise with the proposition that
-- describes all branches returned for it.  The associated proposition is not
-- supplied at a `getMGUs` call site.
class MGUOracle (premise : Prop) where
  branches : Prop

-- A pretheorem packages a completed main proof together with the proposition
-- whose proof is still required to promote it to an ordinary theorem.
structure Pretheorem (conclusion : Prop) where
  Certificate : Prop
  proof : Certificate → conclusion

-- The second goal created while elaborating a `pretheorem` carries the shared
-- certificate metavariable. It is definitionally `True`; its only purpose is
-- to let the finalizer close the accumulated conjunction after the main proof.
private def pendingCertificates (_ : Prop) : Prop := True

/-
`getMGUs h from premise` is generic: instance synthesis selects the oracle
result from the type of `premise`. Inside a `pretheorem`, the tactic makes the
returned branches available as `h` and records the closed coverage proposition
in the pretheorem's certificate. Multiple invocations append more fields to the
same certificate conjunction.

`getMGUs h using first, second` is the higher-level form. It accepts two
equalities that share the matched state, derives the equality between their
symbolic terms, and reduces state-constructor equality before querying the same
oracle machinery.

`getMGUs h matching rule against pattern` is the tuple-level form intended for
users. At a `mapsInto` goal it opens both closure encodings, performs the
semantic bookkeeping internally, and rewrites the target state to the rule RHS.
-/
syntax (name := getMGUsFrom) "getMGUs " ident " from " term : tactic
syntax (name := getMGUsUsing)
  "getMGUs " ident " using " term ", " term : tactic
syntax (name := getMGUsMatching)
  "getMGUs " ident " matching " term " against " term : tactic

private partial def collectFVars
    (expression : Lean.Expr) (found : Array Lean.FVarId := #[]) :
    Array Lean.FVarId :=
  match expression with
  | .fvar id => if found.contains id then found else found.push id
  | .app fn arg => collectFVars arg (collectFVars fn found)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      collectFVars body (collectFVars domain found)
  | .letE _ type value body _ =>
      collectFVars body (collectFVars value (collectFVars type found))
  | .mdata _ body | .proj _ _ body => collectFVars body found
  | _ => found

open Lean Meta Elab Tactic in
private partial def appendCertificate
    (certificateType certificateProof obligation : Expr) : MetaM Expr := do
  let certificateType ← instantiateMVars certificateType
  if let .mvar tail := certificateType then
    let nextTail ←
      mkFreshExprMVar (mkSort .zero) MetavarKind.natural `certificateTail
    tail.assign (mkApp2 (mkConst ``And) obligation nextTail)
    return mkApp3 (mkConst ``And.left) obligation nextTail certificateProof
  let arguments := certificateType.getAppArgs
  if certificateType.getAppFn.isConstOf ``And && arguments.size == 2 then
    let rightProof :=
      mkApp3 (mkConst ``And.right) arguments[0]! arguments[1]! certificateProof
    return ← appendCertificate arguments[1]! rightProof obligation
  throwError "malformed pretheorem certificate accumulator"

open Lean Meta Elab Tactic in
private partial def closeCertificate (certificateType : Expr) : MetaM Unit := do
  let certificateType ← instantiateMVars certificateType
  if let .mvar tail := certificateType then
    tail.assign (mkConst ``True)
    return
  let arguments := certificateType.getAppArgs
  if certificateType.getAppFn.isConstOf ``And && arguments.size == 2 then
    closeCertificate arguments[1]!
  else
    throwError "malformed pretheorem certificate accumulator"

open Lean Meta in
private def closureBinderNames : Expr → List Name
  | .lam name _ body _ => name :: closureBinderNames body
  | _ => []

open Lean Meta in
private partial def unpackExistentials
    (goal : MVarId) (hypothesis : FVarId) (binderNames : List Name) :
    MetaM (MVarId × FVarId) :=
  goal.withContext do
    let hypothesisType ← whnf (← inferType (mkFVar hypothesis))
    unless hypothesisType.getAppFn.isConstOf ``Exists do
      return (goal, hypothesis)
    let subgoals ← goal.cases hypothesis
    let [subgoal] := subgoals.toList
      | throwError "unexpected branching while opening a pattern or rule closure"
    let some field := subgoal.fields.back?
      | throwError "failed to expose a closure body"
    let .fvar bodyHypothesis := field
      | throwError "failed to expose a closure body"
    let goal ← match binderNames, subgoal.fields.toList with
      | name :: _, .fvar witness :: _ => subgoal.mvarId.rename witness name
      | _, _ => pure subgoal.mvarId
    unpackExistentials goal bodyHypothesis binderNames.tail

open Lean Meta in
private def andProjections (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType proof)
  let arguments := type.getAppArgs
  unless type.getAppFn.isConstOf ``And && arguments.size == 2 do
    throwError "expected the atomic tuple semantics to be a conjunction"
  return (mkApp3 (mkConst ``And.left) arguments[0]! arguments[1]! proof,
    mkApp3 (mkConst ``And.right) arguments[0]! arguments[1]! proof)

syntax (name := startPretheorem) "startPretheorem" : tactic
syntax (name := finishPretheorem) "finishPretheorem" : tactic
syntax (name := runPretheoremProof) "runPretheoremProof " term : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic|startPretheorem) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let arguments := target.getAppArgs
      unless target.getAppFn.isConstOf ``Pretheorem && arguments.size == 1 do
        throwError "`startPretheorem` must prove a `Pretheorem`"
      let conclusion := arguments[0]!
      let certificateType ←
        mkFreshExprMVar (mkSort .zero) MetavarKind.natural `certificate
      let proofType ← mkArrow certificateType conclusion
      let proof ←
        mkFreshExprMVar proofType MetavarKind.syntheticOpaque `pretheoremProof
      goal.assign
        (mkApp3 (mkConst ``Pretheorem.mk) conclusion certificateType proof)
      let (certificateHypothesis, mainGoal) ←
        proof.mvarId!.intro `__pretheoremCertificate
      let pendingType :=
        mkApp (mkConst ``pendingCertificates) certificateType
      let pending ←
        mkFreshExprMVar pendingType MetavarKind.syntheticOpaque `certificates
      mainGoal.withContext do
        Term.addTermInfo' (isBinder := true) (← `(ident| __pretheoremCertificate))
          (mkFVar certificateHypothesis)
      replaceMainGoal [mainGoal, pending.mvarId!]
  | `(tactic|finishPretheorem) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let arguments := target.getAppArgs
      unless target.getAppFn.isConstOf ``pendingCertificates && arguments.size == 1 do
        throwError "`finishPretheorem` must close a pretheorem certificate"
      closeCertificate arguments[0]!
      goal.assign (mkConst ``True.intro)
      replaceMainGoal []
  | `(tactic|runPretheoremProof $proof:term) =>
      match proof with
      | `(term|by $tactics:tacticSeq) => evalTactic tactics
      | _ => throwError "a `pretheorem` currently requires a `by` proof"

open Lean Meta Elab Tactic in
private def exposeMGUs (h : TSyntax `ident) (premise : Expr) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  Term.synthesizeSyntheticMVarsNoPostponing
  let premise ← instantiateMVars premise
  let premiseType ← instantiateMVars (← inferType premise)
  let oracleType := mkApp (mkConst ``MGUOracle) premiseType
  let oracle ← synthInstance oracleType
  let branchType :=
    mkApp2 (mkConst ``MGUOracle.branches) premiseType oracle
  let certificateType ← mkArrow premiseType branchType

  let localContext ← getLCtx
  let some certificateDeclaration :=
      localContext.findFromUserName? `__pretheoremCertificate
    | throwError "`getMGUs` must currently be used inside a `pretheorem`"

  -- Close the obligation over precisely the local variables introduced after
  -- the hidden certificate argument on which it depends.
  let mut dependencies := collectFVars certificateType
  let mut changed := true
  while changed do
    changed := false
    for declaration in localContext do
      if dependencies.contains declaration.fvarId then
        let expanded := collectFVars declaration.type dependencies
        let expanded := match declaration.value? with
          | some value => collectFVars value expanded
          | none => expanded
        if expanded.size != dependencies.size then
          dependencies := expanded
          changed := true
  let mut afterCertificate := false
  let mut localVariables := #[]
  for declaration in localContext do
    if declaration.fvarId == certificateDeclaration.fvarId then
      afterCertificate := true
    else if afterCertificate && dependencies.contains declaration.fvarId then
      localVariables := localVariables.push (mkFVar declaration.fvarId)
  let closedCertificateType ←
    mkForallFVars localVariables certificateType

  let rootCertificateType ← inferType (mkFVar certificateDeclaration.fvarId)
  let closedCertificateProof ← appendCertificate rootCertificateType
    (mkFVar certificateDeclaration.fvarId) closedCertificateType
  let certificate := mkAppN closedCertificateProof localVariables
  let branchEvidence := mkApp certificate premise
  let (branchHypothesis, mainGoal) ←
    (← goal.assert h.getId branchType branchEvidence).intro1P
  mainGoal.withContext do
    Term.addTermInfo' (isBinder := true) h (mkFVar branchHypothesis)
  replaceMainGoal [mainGoal]

open Lean Meta Elab Tactic in
private def deriveSharedStateEquality (first second : Expr) : MetaM Expr := do
  let firstType ← whnf (← inferType first)
  let secondType ← whnf (← inferType second)
  let firstArguments := firstType.getAppArgs
  let secondArguments := secondType.getAppArgs
  unless firstType.getAppFn.isConstOf ``Eq && firstArguments.size == 3 &&
      secondType.getAppFn.isConstOf ``Eq && secondArguments.size == 3 do
    throwError "the arguments to `getMGUs ... using` must be equality proofs"
  let firstLeft := firstArguments[1]!
  let firstRight := firstArguments[2]!
  let secondLeft := secondArguments[1]!
  let secondRight := secondArguments[2]!

  let rawProof ←
    if ← isDefEq firstRight secondRight then
      mkEqTrans first (← mkEqSymm second)
    else if ← isDefEq firstRight secondLeft then
      mkEqTrans first second
    else if ← isDefEq firstLeft secondRight then
      mkEqTrans (← mkEqSymm first) (← mkEqSymm second)
    else if ← isDefEq firstLeft secondLeft then
      mkEqTrans (← mkEqSymm first) second
    else
      throwError "the equality proofs given to `getMGUs ... using` do not share a state"

  -- Constructor injectivity and trivial fields are handled by the ordinary
  -- simplifier. `simpType` transports the proof to the simplified proposition,
  -- so this preprocessing remains entirely kernel checked.
  let rawType ← inferType rawProof
  let rawArguments := rawType.getAppArgs
  let environment ← getEnv
  let injectivityLemmas := match rawArguments[1]!.getAppFn with
    | .const constructor _ =>
        let injectivity := Name.str constructor "injEq"
        if environment.contains injectivity then
          [injectivity, ``and_true, ``true_and]
        else
          [``and_true, ``true_and]
    | _ => [``and_true, ``true_and]
  let simpContext ←
    Simp.Context.ofNames injectivityLemmas (simpOnly := true)
  Lean.Meta.simpType (fun expression => do
    return (← simp expression simpContext).1) rawProof

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic|getMGUs $h:ident from $premiseSyntax:term) => withMainContext do
      let premise ← Term.elabTerm premiseSyntax none
      exposeMGUs h premise
  | `(tactic|getMGUs $h:ident using $firstSyntax:term, $secondSyntax:term) =>
      withMainContext do
      let first ← Term.elabTerm firstSyntax none
      let second ← Term.elabTerm secondSyntax none
      Term.synthesizeSyntheticMVarsNoPostponing
      let premise ← deriveSharedStateEquality first second
      exposeMGUs h premise
  | `(tactic|getMGUs $h:ident matching $ruleSyntax:term against $patternSyntax:term) => do
      -- Traverse the existing recursive semantics for closure arguments until
      -- the encoded atomic tuple is reached.
      let (patternBinderNames, ruleBinderNames) ← withMainContext do
        let pattern ← Term.elabTerm patternSyntax none
        let rule ← Term.elabTerm ruleSyntax none
        let pattern ← withTransparency .all <| whnf pattern
        let rule ← withTransparency .all <| whnf rule
        return (closureBinderNames pattern, closureBinderNames rule)
      withMainContext do
        let goal ← getMainGoal
        let (_, goal) ← goal.intro `__before
        let (_, goal) ← goal.intro `__after
        let (_, goal) ← goal.intro `__patternSemantics
        let (_, goal) ← goal.intro `__ruleSemantics
        replaceMainGoal [goal]
      let patternHypothesis := mkIdent `__patternSemantics
      let ruleHypothesis := mkIdent `__ruleSemantics
      let simplifySemantics ←
        `(tactic| simp only [Pattern.semantics, AtPattern.semantics, Rule.semantics, AtRule.semantics, $patternSyntax:term, $ruleSyntax:term] at $patternHypothesis:ident $ruleHypothesis:ident)
      evalTactic simplifySemantics

      let (patternBody, ruleBody) ← withMainContext do
        let goal ← getMainGoal
        let localContext ← getLCtx
        let some patternDeclaration :=
            localContext.findFromUserName? `__patternSemantics
          | throwError "failed to find the pattern-semantics hypothesis"
        let (goal, patternBody) ←
          unpackExistentials goal patternDeclaration.fvarId patternBinderNames
        let ruleDeclaration ← goal.withContext do
          let some declaration :=
              (← getLCtx).findFromUserName? `__ruleSemantics
            | throwError "failed to find the rule-semantics hypothesis"
          return declaration
        let (goal, ruleBody) ←
          unpackExistentials goal ruleDeclaration.fvarId ruleBinderNames
        replaceMainGoal [goal]
        return (patternBody, ruleBody)

      withMainContext do
        let patternProof := mkFVar patternBody
        let ruleProof := mkFVar ruleBody
        let (patternStateEquality, _) ← andProjections patternProof
        let (ruleLhsEquality, ruleTail) ← andProjections ruleProof
        let (ruleRhsEquality, _) ← andProjections ruleTail
        let premise ←
          deriveSharedStateEquality ruleLhsEquality patternStateEquality
        exposeMGUs h premise

        -- Replace the concrete `after` state by the rule's symbolic RHS. The
        -- remaining goal is now stated solely in tuple-level symbolic terms.
        let goal ← getMainGoal
        let ruleRhsType ← inferType ruleRhsEquality
        let (_, goal) ←
          (← goal.assert `__ruleRhsEquality ruleRhsType ruleRhsEquality).intro1P
        replaceMainGoal [goal]
      let after := mkIdent `__after
      evalTactic (← `(tactic| subst $after:ident))

syntax (name := pretheoremCommand)
  "pretheorem " ident " : " term " := " term : command

macro_rules
  | `(pretheorem $name:ident : $conclusion:term := $proof:term) =>
      `(def $name : Pretheorem $conclusion := by
          startPretheorem
          · runPretheoremProof $proof
          · finishPretheorem)

-- Minimality of postImage (strongestness).
theorem mapsInto_iff_postImage_subset
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [Rule α R]
    (r : R) (patt0 : P) (target : Q) :
    mapsInto (α := α) r patt0 target ↔
      ∀ (after : α), postImage (α := α) r patt0 after →
        Pattern.semantics target after := by
  constructor
  · rintro h after ⟨before, hpatt0, hstep⟩
    exact h before after hpatt0 hstep
  · intro h before after hpatt0 hstep
    exact h after ⟨before, hpatt0, hstep⟩

end framework


namespace ex1

open framework
open scoped Disjunction

structure Conf where
  n : Nat
  m : Nat

instance : State Conf := ⟨⟩

def patt0 (n : Nat) : Conf × Prop :=
  (⟨0, n⟩, True)

def rule1 (n : Nat) : Conf × Conf × Prop :=
  ⟨⟨0, n⟩, ⟨n, 0⟩, n < 3⟩

def rule2 (n m : Nat) : Conf × Conf × Prop :=
  ⟨⟨0, n⟩, ⟨n, 1⟩, 3 ≤ n ∧ m = 0⟩

def rules :=
  rule1 ⊔ rule2

def computedPost :=
  (fun n : Nat => ((⟨n, 0⟩ : Conf), n < 3)) ⊔
  (fun n m : Nat => ((⟨n, 1⟩ : Conf), 3 ≤ n ∧ m = 0))

#print computedPost

theorem computedPost_is_postImage :
    postImage (α := Conf) rules patt0 =
      Pattern.denotes computedPost := by
  funext state
  simp [postImage, Pattern.denotes, AtPattern.semantics, Pattern.semantics,
    AtRule.semantics, Rule.semantics,
    Conf.mk.injEq, rules, patt0, rule1, rule2,
    computedPost]
  constructor
  · rintro ⟨a, ha | ha⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, ha⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨a, Or.inl ha⟩
    · exact ⟨a, Or.inr ha⟩

-- A sound but non-minimal over-approximation with an extra branch.
def largerPost :=
  computedPost ⊔ (fun n : Nat => ((⟨n, 2⟩ : Conf), True))

theorem rules_map_patt0_into_largerPost :
    mapsInto (α := Conf) rules patt0 largerPost := by
  rw [mapsInto_iff_postImage_subset]
  intro state hpost
  rw [computedPost_is_postImage] at hpost
  exact Or.inl hpost

theorem largerPost_is_not_postImage :
    postImage (α := Conf) rules patt0 ≠
      Pattern.denotes largerPost := by
  intro heq
  have hextra : Pattern.denotes largerPost (⟨0, 2⟩ : Conf) := by
    simp [Pattern.denotes, largerPost, computedPost,
      AtPattern.semantics, Pattern.semantics, Conf.mk.injEq]
  have hpost : postImage (α := Conf) rules patt0 ⟨0, 2⟩ := by
    rw [heq]
    exact hextra
  rw [computedPost_is_postImage] at hpost
  simp [Pattern.denotes, computedPost, AtPattern.semantics, Pattern.semantics,
    Conf.mk.injEq] at hpost

end ex1


namespace ex2

open framework

structure Conf where
  n : Multiset Nat

instance : State Conf := ⟨⟩

def pat (X Y : Multiset Nat) : Conf × Prop :=
  ⟨⟨X + Y + {2}⟩, True⟩

def rule (Z : Multiset Nat) : Conf × Conf × Prop :=
  ⟨⟨{1} + Z⟩, ⟨Z⟩, True⟩

def computedPost (W : Multiset Nat) : Conf × Prop :=
  ⟨⟨W + {2}⟩, True⟩

theorem computedPost_is_postImage :
    postImage (α := Conf) rule pat =
      Pattern.denotes computedPost := by
  funext after
  simp [postImage, Pattern.denotes, AtPattern.semantics, Pattern.semantics,
    AtRule.semantics, Rule.semantics, Conf.mk.injEq,
    pat, rule, computedPost]
  constructor
  · rintro ⟨X, Y, Z, hac, hafter⟩
    have hmem : 2 ∈ Z := by
      have : 2 ∈ 1 ::ₘ Z := by
        rw [hac]
        simp
      simpa using this
    obtain ⟨W, hZ⟩ := Multiset.exists_cons_of_mem hmem
    refine ⟨W, ?_⟩
    rw [← hafter]
    congr 1
    rw [hZ, ← Multiset.singleton_add, Multiset.add_comm]
  · rintro ⟨W, hafter⟩
    refine ⟨{1}, W, W + {2}, ?_, hafter⟩
    rw [← Multiset.singleton_add, Multiset.add_assoc]

end ex2


namespace ex3

open framework
open scoped Disjunction

structure Conf where
  source : Multiset Nat
  left : Multiset Nat
  right : Multiset Nat

instance : State Conf := ⟨⟩

def pat (Z : Multiset Nat) : Conf × Prop :=
  ⟨⟨{1} + Z, ∅, ∅⟩, True⟩

def rule (X Y : Multiset Nat) : Conf × Conf × Prop :=
  ⟨⟨X + Y + {2}, ∅, ∅⟩, ⟨∅, X, Y⟩, True⟩

def computedPost :=
  (fun U₁ U₂ : Multiset Nat =>
    ((⟨∅, U₂ + {1}, U₁⟩ : Conf), True)) ⊔
  (fun U₁ U₂ : Multiset Nat =>
    ((⟨∅, U₁, U₂ + {1}⟩ : Conf), True))

-- Dummy result currently returned by `getMGUs` for this shape of AC equation.
-- It is registered with the generic tactic machinery rather than named or
-- supplied by the `mapsInto` proof.
private instance dummyACResult (X Y Z : Multiset Nat) :
    MGUOracle (X + Y + {2} = {1} + Z) where
  branches :=
    (∃ U₁ U₂ : Multiset Nat,
      X = U₂ + {1} ∧ Y = U₁ ∧ Z = U₁ + U₂ + {2}) ∨
    (∃ U₁ U₂ : Multiset Nat,
      X = U₁ ∧ Y = U₂ + {1} ∧ Z = U₁ + U₂ + {2})

--- pretheorem: unknown_certificate → rule(pat) ⊑ computedPost
pretheorem rule_pat_into_computedPost_pre :
    mapsInto (α := Conf) rule pat computedPost := by
  getMGUs hMGUs matching rule against pat
  rcases hMGUs with hbranch | hbranch
  · left
    rcases hbranch with ⟨U₁, U₂, hX, hY, -⟩
    refine ⟨U₁, U₂, ?_⟩
    simp [AtPattern.semantics, computedPost, hX, hY]
  · right
    rcases hbranch with ⟨U₁, U₂, hX, hY, -⟩
    refine ⟨U₁, U₂, ?_⟩
    simp [AtPattern.semantics, computedPost, hX, hY]

#print rule_pat_into_computedPost_pre

--- providing certificate promotes pretheorems to theorems
--- theorem: rule(pat) ⊑ computedPost
theorem rule_pat_into_computedPost :
    mapsInto (α := Conf) rule pat computedPost :=
  rule_pat_into_computedPost_pre.proof sorry


-- The main proof above determines this proposition. Its proof is deliberately
-- supplied afterward, so development can proceed before the oracle result has
-- been certified.
theorem rule_pat_into_computedPost_certificate :
    rule_pat_into_computedPost_pre.Certificate := by
  sorry

theorem computedPost_is_postImage :
    postImage (α := Conf) rule pat =
      Pattern.denotes computedPost := by
  funext after
  -- Unfolding the semantic instances reduces exactness of the post-image to
  -- exactness of the two AC-unifier branches in `computedPost`.
  simp [postImage, Pattern.denotes, AtPattern.semantics, Pattern.semantics,
    AtRule.semantics, Rule.semantics, Conf.mk.injEq,
    pat, rule, computedPost]
  constructor
  -- Completeness of the unifiers: take an arbitrary solution of the matching
  -- equation
  --
  --     X + Y + {2} = {1} + Z.
  --
  -- Since the right-hand side contains `1`, the left-hand side does too.
  -- Because `1 ≠ 2`, that occurrence must come from either `X` or `Y`.
  -- These two exhaustive cases are precisely the two branches generated by
  -- AC-unification.
  · rintro ⟨Z, X, Y, hac, rfl⟩
    have hmem : 1 ∈ X + Y + {2} := by
      rw [hac]
      simp
    have hXY : 1 ∈ X ∨ 1 ∈ Y := by
      simpa using hmem
    rcases hXY with hX | hY
    -- First complete-unifier branch:
    --
    --     X = U₂ + {1},  Y = U₁,
    --     Z = U₁ + U₂ + {2}.
    --
    -- Decomposing `1 ∈ X` supplies the residual multiset `U` playing `U₂`;
    -- the current `Y` plays `U₁`.
    · obtain ⟨U, hX⟩ := Multiset.exists_cons_of_mem hX
      left
      refine ⟨Y, U, ?_⟩
      congr 1
      rw [hX, ← Multiset.singleton_add, Multiset.add_comm]
    -- Second complete-unifier branch, symmetrically:
    --
    --     X = U₁,  Y = U₂ + {1},
    --     Z = U₁ + U₂ + {2}.
    · obtain ⟨U, hY⟩ := Multiset.exists_cons_of_mem hY
      right
      refine ⟨X, U, ?_⟩
      congr 1
      rw [hY, ← Multiset.singleton_add, Multiset.add_comm]
  -- Soundness of the unifiers: every state described by either computed
  -- branch must arise from a genuine match and rule step.  For each branch we
  -- instantiate `X`, `Y`, and `Z` with the reported substitution and verify
  -- the matching equation using associativity and commutativity of multiset
  -- addition.
  · rintro (⟨U₁, U₂, hafter⟩ | ⟨U₁, U₂, hafter⟩)
    -- Validate X = U₂ + {1}, Y = U₁, Z = U₁ + U₂ + {2}.
    · refine ⟨U₁ + U₂ + {2}, U₂ + {1}, U₁, ?_, hafter⟩
      rw [← Multiset.singleton_add]
      calc
        U₂ + {1} + U₁ + {2} = ({1} + U₂) + U₁ + {2} := by
          rw [Multiset.add_comm U₂ {1}]
        _ = {1} + (U₂ + U₁ + {2}) := by
          rw [Multiset.add_assoc {1} U₂ U₁,
            Multiset.add_assoc {1} (U₂ + U₁) {2}]
        _ = {1} + (U₁ + U₂ + {2}) := by
          rw [Multiset.add_comm U₂ U₁]
    -- Validate X = U₁, Y = U₂ + {1}, Z = U₁ + U₂ + {2}.
    · refine ⟨U₁ + U₂ + {2}, U₁, U₂ + {1}, ?_, hafter⟩
      rw [← Multiset.singleton_add]
      calc
        U₁ + (U₂ + {1}) + {2} = (U₂ + {1}) + U₁ + {2} := by
          rw [Multiset.add_comm U₁ (U₂ + {1})]
        _ = ({1} + U₂) + U₁ + {2} := by
          rw [Multiset.add_comm U₂ {1}]
        _ = {1} + (U₂ + U₁ + {2}) := by
          rw [Multiset.add_assoc {1} U₂ U₁,
            Multiset.add_assoc {1} (U₂ + U₁) {2}]
        _ = {1} + (U₁ + U₂ + {2}) := by
          rw [Multiset.add_comm U₂ U₁]

end ex3




namespace experimental
universe u v w

structure Conf where
  n : Nat
  m : Nat
--instance : State Conf := ⟨⟩

structure MetaPattern where
  term : Lean.Expr
  cond : Lean.Expr

structure RewriteRule where
  lhs : Conf
  rhs : Conf
  cond : Prop

structure MetaRule where
  lhs : Lean.Expr
  rhs : Lean.Expr
  cond : Lean.Expr

def pat1 (n m : Nat) : Conf × Prop :=
  (⟨n, m⟩, n > m)

def pat2 (m : Nat) : Conf × Prop :=
  (⟨0, m⟩, True)

def pat2' (m n : Nat) : Conf × Prop :=
  (⟨m, n⟩, n < 4)
#check pat2'

def pat3 (n m _unused : Nat) : Conf × Prop :=
  (⟨n, m⟩, n > m)

def toMeta (p : Lean.Expr) : Lean.Meta.MetaM MetaPattern := do
  let (vars, _, resultType) ← Lean.Meta.forallMetaTelescopeReducing
    (← Lean.Meta.inferType p)
  let expectedType ← Lean.Meta.mkAppM ``Prod
    #[Lean.mkConst ``Conf, Lean.mkSort .zero]
  unless ← Lean.Meta.isDefEq resultType expectedType do
    throwError "expected a pattern returning Conf × Prop, got {resultType}"
  let value ← Lean.Meta.whnf (Lean.mkAppN p vars)
  let termProj ← Lean.Meta.mkAppM ``Prod.fst #[value]
  let condProj ← Lean.Meta.mkAppM ``Prod.snd #[value]
  let some term ← Lean.Expr.reduceProjStruct? termProj
    | throwError "could not extract the pattern term"
  let some cond ← Lean.Expr.reduceProjStruct? condProj
    | throwError "could not extract the pattern condition"
  return ⟨term, cond⟩

elab "#toMeta " p:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let objectPattern ← Lean.Elab.Term.elabTerm p none
    let pattern ← toMeta objectPattern
    Lean.logInfo m!"{pattern.term} where {pattern.cond}"

#toMeta pat1
#toMeta pat2
#toMeta pat3

class PatternSemantics (P : Type u) where
  denotes : P → Conf → Prop

instance : PatternSemantics (Conf × Prop) where
  denotes p state := p.snd ∧ p.fst = state

instance {A : Type u} {P : Type v} [PatternSemantics P] :
    PatternSemantics (A → P) where
  denotes p state := ∃ x, PatternSemantics.denotes (p x) state

def denotesDisjunction {P : Type u} [PatternSemantics P]
    (patterns : List P) (state : Conf) : Prop :=
  ∃ pattern ∈ patterns, PatternSemantics.denotes pattern state

instance {P : Type u} [PatternSemantics P] :
    PatternSemantics (List P) where
  denotes := fun (patterns : List P) (state : Conf) =>
    ∃ pattern ∈ patterns, PatternSemantics.denotes pattern state
  --denotes := denotesDisjunction



class RuleSemantics (R : Type u) where
  steps : R → Conf → Conf → Prop

instance : RuleSemantics RewriteRule where
  steps r before after :=
    r.cond ∧ before = r.lhs ∧ after = r.rhs

instance {A : Type u} {R : Type v} [RuleSemantics R] :
    RuleSemantics (A → R) where
  steps r before after := ∃ x, RuleSemantics.steps (r x) before after

instance {R : Type u} [RuleSemantics R] : RuleSemantics (List R) where
  steps rules before after :=
    ∃ rule ∈ rules, RuleSemantics.steps rule before after



def postImage {P : Type u} {R : Type v}
    [PatternSemantics P] [RuleSemantics R]
    (r : R) (patt0 : P) : Conf → Prop :=
  fun after =>
    ∃ before,
      PatternSemantics.denotes patt0 before ∧
      RuleSemantics.steps r before after

def mapsInto {P : Type u} {Q : Type v} {R : Type w}
    [PatternSemantics P] [PatternSemantics Q] [RuleSemantics R]
    (r : R) (patt0 : P) (target : Q) : Prop :=
  ∀ before after,
    PatternSemantics.denotes patt0 before →
    RuleSemantics.steps r before after →
    PatternSemantics.denotes target after

-- minimality of postImage (strongestness)
theorem mapsInto_iff_postImage_subset
    {P : Type u} {Q : Type v} {R : Type w}
    [PatternSemantics P] [PatternSemantics Q] [RuleSemantics R]
    (r : R) (patt0 : P) (target : Q) :
    mapsInto r patt0 target ↔
      ∀ after, postImage r patt0 after →
        PatternSemantics.denotes target after := by
  constructor
  · rintro h after ⟨before, hpatt0, hstep⟩
    exact h before after hpatt0 hstep
  · intro h before after hpatt0 hstep
    exact h after ⟨before, hpatt0, hstep⟩


def toMetaRule (r : Lean.Expr) : Lean.Meta.MetaM MetaRule := do
  let (vars, _, resultType) ← Lean.Meta.forallMetaTelescopeReducing
    (← Lean.Meta.inferType r)
  unless ← Lean.Meta.isDefEq resultType (Lean.mkConst ``RewriteRule) do
    throwError "expected a function returning RewriteRule, got {resultType}"
  let value ← Lean.Meta.whnf (Lean.mkAppN r vars)
  let lhsProj ← Lean.Meta.mkAppM ``RewriteRule.lhs #[value]
  let rhsProj ← Lean.Meta.mkAppM ``RewriteRule.rhs #[value]
  let condProj ← Lean.Meta.mkAppM ``RewriteRule.cond #[value]
  let some lhs ← Lean.Expr.reduceProjStruct? lhsProj
    | throwError "could not extract the rule's left-hand side"
  let some rhs ← Lean.Expr.reduceProjStruct? rhsProj
    | throwError "could not extract the rule's right-hand side"
  let some cond ← Lean.Expr.reduceProjStruct? condProj
    | throwError "could not extract the rule's condition"
  return ⟨lhs, rhs, cond⟩

elab "#toMetaRule " r:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let objectRule ← Lean.Elab.Term.elabTerm r none
    let rule ← toMetaRule objectRule
    Lean.logInfo m!"{rule.lhs} => {rule.rhs} if {rule.cond}"


-- ⟨0, n⟩ → ⟨n, m⟩ if m < 3
def rule1 (n m : Nat) : RewriteRule :=
  ⟨⟨0, n⟩, ⟨n, m⟩, m < 3⟩

#toMetaRule rule1

theorem rule1_maps_pat2_into_pat2' : mapsInto rule1 pat2 pat2' := by
  intro before after _ step
  obtain ⟨n, m, hm, _, hafter⟩ := step
  refine ⟨n, m, ?_, ?_⟩
  · simp [pat2']
    simp [rule1] at hm
    omega
  · simpa [rule1, pat2'] using hafter.symm





namespace example1

def patt0 (n : Nat) : Conf × Prop :=
  (⟨0, n⟩, True)

def rule1 (n : Nat) : RewriteRule :=
  ⟨⟨0, n⟩, ⟨n, 0⟩, n < 3⟩

def rule2 (n : Nat) : RewriteRule :=
  ⟨⟨0, n⟩, ⟨n, 1⟩, 3 ≤ n⟩

def rules : List (Nat → RewriteRule) :=
  [rule1, rule2]

-- Hardcoded stand-in for the disjunction computed by DM-Check.
-- ((< 0, $1:Nat >) | ((true).NuITP-Bool)) \/
-- ((< $2:Nat, s 0 >) | (true /\ s_^3(0) <= $2:Nat = (true).Bool)) \/
-- ((< $3:Nat, 0 >) | (true /\ $3:Nat < s_^3(0) = (true).Bool))
def computedPost : List (Nat → Conf × Prop) :=
  [fun n => (⟨n, 0⟩, n < 3),
   fun n => (⟨n, 1⟩, 3 ≤ n)]

theorem computedPost_is_postImage :
    postImage rules patt0 =
      denotesDisjunction computedPost := by
  funext state
  simp [postImage, denotesDisjunction, PatternSemantics.denotes,
    RuleSemantics.steps, rules, patt0, rule1, rule2,
    computedPost]
  aesop

-- A sound but non-minimal over-approximation with an extra branch.
def largerPost : List (Nat → Conf × Prop) :=
  computedPost ++ [fun n => (⟨n, 2⟩, True)]

theorem rules_map_patt0_into_largerPost :
    mapsInto rules patt0 largerPost := by
  rw [mapsInto_iff_postImage_subset]
  intro state hpost
  rw [computedPost_is_postImage] at hpost
  change denotesDisjunction largerPost state
  obtain ⟨pattern, hmem, hstate⟩ := hpost
  exact ⟨pattern, by simp [largerPost, hmem], hstate⟩

theorem largerPost_is_not_postImage :
    postImage rules patt0 ≠ denotesDisjunction largerPost := by
  intro heq
  have hextra : denotesDisjunction largerPost ⟨0, 2⟩ := by
    refine ⟨fun n => (⟨n, 2⟩, True), ?_, ?_⟩
    · simp [largerPost]
    · exact ⟨0, True.intro, rfl⟩
  have hpost : postImage rules patt0 ⟨0, 2⟩ := by
    rw [heq]
    exact hextra
  rw [computedPost_is_postImage] at hpost
  simp [denotesDisjunction, computedPost,
    PatternSemantics.denotes] at hpost

end example1
end experimental
