import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

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

instance {α : Type u} {P : Type v} [State α] [AtPattern α P] :
    Pattern α P where
  semantics := AtPattern.semantics

structure PatternDisjunction (P : Type v) (Q : Type w) where
  left : P
  right : Q

scoped[Pattern] infixr:65 " ⊔ " => framework.PatternDisjunction.mk

instance {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q] :
    Pattern α (PatternDisjunction P Q) where
  semantics patterns state :=
    Pattern.semantics patterns.left state ∨
    Pattern.semantics patterns.right state

theorem Pattern.disjunction_assoc
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [Pattern α R]
    (p : P) (q : Q) (r : R) (state : α) :
    Pattern.semantics (PatternDisjunction.mk (PatternDisjunction.mk p q) r) state ↔
      Pattern.semantics (PatternDisjunction.mk p (PatternDisjunction.mk q r)) state := by
  change
    (Pattern.semantics p state ∨ Pattern.semantics q state) ∨
        Pattern.semantics r state ↔
      Pattern.semantics p state ∨
        (Pattern.semantics q state ∨ Pattern.semantics r state)
  exact or_assoc



-- R is a type of rules denoting transitions between α-states.
class Rule (α : Type u) [State α] (R : Type v) where
  semantics : R → α → α → Prop

instance {α : Type u} [State α] : Rule α (α × α × Prop) where
  semantics r before after :=
    r.1 = before ∧ r.2.1 = after ∧ r.2.2

instance {α : Type u} {A : Type v} {R : Type w}
    [State α] [Rule α R] : Rule α (A → R) where
  semantics r before after := ∃ x, Rule.semantics (r x) before after

instance {α : Type u} {R : Type v} [State α] [Rule α R] :
    Rule α (List R) where
  semantics rules before after :=
    ∃ rule ∈ rules, Rule.semantics rule before after



def postImage {α : Type u} {P : Type v} {R : Type w}
    [State α] [Pattern α P] [Rule α R]
    (r : R) (patt0 : P) : α → Prop :=
  fun after =>
    ∃ before,
      Pattern.semantics patt0 before ∧
      Rule.semantics r before after

def mapsInto
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [Rule α R]
    (r : R) (patt0 : P) (target : Q) : Prop :=
  ∀ (before after : α),
    Pattern.semantics patt0 before →
    Rule.semantics r before after →
    Pattern.semantics target after

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
open scoped Pattern

structure Conf where
  n : Nat
  m : Nat

instance : State Conf := ⟨⟩

def patt0 (n : Nat) : Conf × Prop :=
  (⟨0, n⟩, True)

def rule1 (n : Nat) : Conf × Conf × Prop :=
  ⟨⟨0, n⟩, ⟨n, 0⟩, n < 3⟩

def rule2 (n : Nat) : Conf × Conf × Prop :=
  ⟨⟨0, n⟩, ⟨n, 1⟩, 3 ≤ n⟩

def rules : List (Nat → Conf × Conf × Prop) :=
  [rule1, rule2]

-- Hardcoded stand-in for the disjunction computed by DM-Check.
-- ((< 0, $1:Nat >) | ((true).NuITP-Bool)) \/
-- ((< $2:Nat, s 0 >) | (true /\ s_^3(0) <= $2:Nat = (true).Bool)) \/
-- ((< $3:Nat, 0 >) | (true /\ $3:Nat < s_^3(0) = (true).Bool))
def computedPost :=
  (fun n : Nat => ((⟨n, 0⟩ : Conf), n < 3)) ⊔
  (fun n m : Nat => ((⟨n, 1⟩ : Conf), 3 ≤ n ∧ m = 0))

theorem computedPost_is_postImage :
    postImage (α := Conf) rules patt0 =
      @Pattern.semantics Conf inferInstance _ inferInstance computedPost := by
  funext state
  simp [postImage, AtPattern.semantics, Pattern.semantics, Rule.semantics,
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
      @Pattern.semantics Conf inferInstance _ inferInstance largerPost := by
  intro heq
  have hextra : @Pattern.semantics Conf inferInstance _ inferInstance
      largerPost ⟨0, 2⟩ := by
    exact Or.inr ⟨0, rfl, True.intro⟩
  have hpost : postImage (α := Conf) rules patt0 ⟨0, 2⟩ := by
    rw [heq]
    exact hextra
  rw [computedPost_is_postImage] at hpost
  simp [computedPost, AtPattern.semantics, Pattern.semantics,
    Conf.mk.injEq] at hpost

end ex1




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
