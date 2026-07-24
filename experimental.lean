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

def denotesDisjunction {P : Type u} [PatternSemantics P]
    (patterns : List P) (state : Conf) : Prop :=
  ∃ pattern ∈ patterns, PatternSemantics.denotes pattern state

instance {P : Type u} [PatternSemantics P] :
    PatternSemantics (List P) where
  denotes := denotesDisjunction

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










namespace try1
class Returns (T : Sort u) (F : Sort v) : Prop where

instance returnsBase (T : Sort u) :
    Returns T T where

instance returnsArrow
    {T : Sort u} {A : Sort v} {R : Sort w}
    [Returns T R] :
    Returns T (A → R) where

example : Returns Nat Nat := by
  infer_instance

example : Returns Nat (Bool → Nat) := by
  infer_instance

example : Returns Nat (Bool → String → Nat) := by
  infer_instance

example : Returns Nat (Bool → String → Unit → Nat) := by
  infer_instance

structure Conf where
  n : Nat
  m : Nat
instance : State Conf := ⟨⟩

#reduce fun (n : Nat) (m : Nat) ↦ ((⟨n, m⟩ : Conf), (n > m))
#check fun (n : Nat) (m : Nat) (_ : n > m) ↦ (⟨n, m⟩ : Conf)

def pat1 := fun (x : Nat × Nat) ↦ ((⟨x.1, x.2⟩, x.1 > x.2) : Conf × Prop)
def pat2 := fun (x : Nat × Nat) ↦ ((⟨x.2, x.1⟩, x.2 > x.1) : Conf × Prop)
def pat3 := fun (_ : Nat × Nat) ↦ ((⟨4,3⟩, true) : Conf × Prop)
def pat4 := fun (x : Nat × Nat) ↦ ((⟨x.2, x.1⟩, x.2 < x.1) : Conf × Prop)

-- ⟨ 0, n ⟩ -> ⟨ n, m ⟩ if m < 3
def rule1? {Ctx : Type u} (p : Ctx → Conf × Prop) :
    Ctx × Nat → Option (Conf × Prop) :=
  fun (ctx, x3) =>
    match p ctx with
    | (⟨0, x2⟩, cond) => some (⟨x2, x3⟩, cond ∧ x3 < 3)
    | _ => none



-- example : swapPattern pat1 = pat4 := by
--   funext x
--   simp [swapPattern, pat1, pat4]


def instanceOf {α : Sort u} (t : Conf) (p : α → Conf × Prop) : Prop :=
  ∃ x, (p x).fst = t ∧ (p x).snd

infix:50 " ∈ " => instanceOf

def subsumedBy' {α : Sort u} (p1 p2 : α → Conf × Prop) : Prop :=
  ∀ t, t ∈ p1 → t ∈ p2

def subsumedBy {α : Sort u} (p1 p2 : α → Conf × Prop) : Prop :=
  ∀ x, (p1 x).snd → ∃ y, (p2 y).snd ∧ (p1 x).fst = (p2 y).fst

theorem subsumedBy'_iff_subsumedBy {α : Sort u}
    (p1 p2 : α → Conf × Prop) :
    subsumedBy' p1 p2 ↔ subsumedBy p1 p2 := by
  constructor
  · intro h x hx
    obtain ⟨y, hyt, hy⟩ :=
      h (p1 x).fst ⟨x, rfl, hx⟩
    exact ⟨y, hy, hyt.symm⟩
  · intro h t ht
    obtain ⟨x, hxt, hx⟩ := ht
    obtain ⟨y, hy, hxy⟩ := h x hx
    exact ⟨y, hxy.symm.trans hxt, hy⟩

infix:50 " ⊑ " => subsumedBy

-- `pat2` describes the same configurations as `pat1`, using swapped inputs.
example : pat1 ⊑ pat2 := by
  intro x hx
  refine ⟨(x.2, x.1), ?_⟩
  simpa [pat1, pat2] using hx

example : pat2 ⊑ pat1 := by
  intro x hx
  refine ⟨(x.2, x.1), ?_⟩
  simpa [pat1, pat2] using hx

-- `pat4` produces configurations whose first component is smaller, so they
-- cannot be covered by `pat1`.
example : ¬(pat4 ⊑ pat1) := by
  intro h
  obtain ⟨y, hy, hconf⟩ := h (2, 1) (by simp [pat4])
  obtain ⟨a, b⟩ := y
  simp [pat4, pat1] at hy hconf
  omega

-- The concrete pattern is covered by `pat1`.
example : pat3 ⊑ pat1 := by
  intro _ _
  exact ⟨(4, 3), by simp [pat1, pat3]⟩

example : ¬(pat3 ⊑ pat4) := by
  intro h
  obtain ⟨y, hy, hconf⟩ := h (0, 0) (by simp [pat3])
  obtain ⟨a, b⟩ := y
  simp [pat3, pat4] at hy hconf
  omega

-- `pat1` is not covered by the single configuration in `pat3`.
example : ¬(pat1 ⊑ pat3) := by
  intro h
  obtain ⟨y, _, hconf⟩ := h (1, 0) (by simp [pat1])
  simp [pat1, pat3] at hconf

-- Two distinct concrete configurations do not subsume one another.
example : ¬(
    (fun _ : Unit => (⟨0, 0⟩, True))
      ⊑ (fun _ : Unit => (⟨1, 1⟩, True))) := by
  intro h
  obtain ⟨y, _, hconf⟩ := h () trivial
  simp at hconf

end try1
