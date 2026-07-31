import Bakery.DMC3

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub


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
