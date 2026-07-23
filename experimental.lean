import Bakery.DMC3

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub


universe u v w

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

def subsumedBy {α : Sort u} (p1 p2 : α → Conf × Prop) : Prop :=
  ∀ x, (p1 x).snd → ∃ y, (p2 y).snd ∧ (p1 x).fst = (p2 y).fst

-- `pat2` describes the same configurations as `pat1`, using swapped inputs.
example : subsumedBy pat1 pat2 := by
  intro x hx
  refine ⟨(x.2, x.1), ?_⟩
  simpa [pat1, pat2] using hx

example : subsumedBy pat2 pat1 := by
  intro x hx
  refine ⟨(x.2, x.1), ?_⟩
  simpa [pat1, pat2] using hx

-- `pat4` produces configurations whose first component is smaller, so they
-- cannot be covered by `pat1`.
example : ¬subsumedBy pat4 pat1 := by
  intro h
  obtain ⟨y, hy, hconf⟩ := h (2, 1) (by simp [pat4])
  obtain ⟨a, b⟩ := y
  simp [pat4, pat1] at hy hconf
  omega

-- The concrete pattern is covered by `pat1`.
example : subsumedBy pat3 pat1 := by
  intro _ _
  exact ⟨(4, 3), by simp [pat1, pat3]⟩

-- `pat1` is not covered by the single configuration in `pat3`.
example : ¬subsumedBy pat1 pat3 := by
  intro h
  obtain ⟨y, _, hconf⟩ := h (1, 0) (by simp [pat1])
  simp [pat1, pat3] at hconf

-- Two distinct concrete configurations do not subsume one another.
example : ¬subsumedBy
    (fun _ : Unit => (⟨0, 0⟩, True))
    (fun _ : Unit => (⟨1, 1⟩, True)) := by
  intro h
  obtain ⟨y, _, hconf⟩ := h () trivial
  simp at hconf

def p := fun {n : Nat} {m : Nat} ↦ ((⟨n, m⟩, n > m) : Conf × Prop)
def p2 := fun {n : Nat} {m : Nat} ↦ ((⟨n, m⟩, n > m + 3) : Conf × Prop)
def t : Conf := ⟨4, 3⟩
def t' : Conf × Prop := (⟨4,3⟩, true)


def subsumedBy' (p1 p2 : Conf × Prop) : Prop :=
  p1.fst = p2.fst ∧ p1.snd → p2.snd

example : subsumedBy' t' (p (n := 4) (m := 3)) := by
  simp [subsumedBy', t', p]

example {n m : Nat} :
    subsumedBy' (p2 (n := n) (m := m)) (p (n := n) (m := m)) := by
  simp [subsumedBy', p2, p]
  omega


#check p
#check t -- Conf




-- t ∈ p iff t = p _ _ ... _
def gInstOf (t : Conf) (p : Conf × Prop) : Prop :=
  t = p.fst











namespace old2
structure Conf where
  n : Nat
  m : Multiset Nat
instance : State Conf := ⟨⟩

/--
`term` and `cond` are indices rather than fields so that they remain visible in
the type of a pattern.  In particular, when a pattern such as `p1` is used
against a ground term, Lean can unify the indexed term with that ground term
and infer the pattern's implicitly quantified variables.  Indexing `cond` also
lets dependent functions recover the symbolic constraint without storing or
proving it; if these were ordinary fields, the implicit variables would not
occur in the result type and could not be inferred this way.
-/
structure AtPatt {α : Type u} [State α] (term : α) (cond : Prop) where
abbrev Patt (α : Type u) [State α] :=
  List (Σ term : α, Σ cond : Prop, AtPatt term cond)


def p1 {n : Nat} {m : Multiset Nat} :
    AtPatt (α := Conf) ⟨n, m⟩ (n > 3) := ⟨⟩

/-- Both the ground term and its constraint are recovered from the indices. -/
def gMatch (ground : Conf) {cond : Prop}
    (_p : AtPatt ground cond) : Prop :=
  cond

example : gMatch ⟨4, ∅⟩ p1 := by
  simp [gMatch]

example : ¬gMatch ⟨3, ∅⟩ p1 := by
  simp [gMatch]

#check p1
#reduce p1
#reduce @p1
#reduce (fun (n : Nat) (m : Multiset Nat) ↦
  ([⟨⟨n, m⟩, n > 3, p1⟩] : Patt Conf))

#check (fun
    {n₁ : Nat} {m₁ : Multiset Nat}
    {n₂ : Nat} {m₂ : Multiset Nat} ↦
  ([ ⟨⟨n₁, m₁⟩, n₁ > 3, p1 (n := n₁) (m := m₁)⟩,
     ⟨⟨n₂, m₂⟩, n₂ > 3, p1 (n := n₂) (m := m₂)⟩
   ] : Patt Conf))


end old2




namespace old1

-- atomic patterns
structure AtPatt (α : Type u) where
  {Vars : Type v}
  term : Vars → α
  cond : Vars → Prop
  --s {n : Nat} {m : Multiset Nat} : patt1 ⟨n, m⟩ (n > 3)

-- def patt1Anon : AtPatt Conf where
--   term := fun (x : Nat × Multiset Nat) =>
--     ⟨x.1, x.2⟩
--   cond := fun x =>
--     x.1 > 3

end old1

namespace old
structure Conf where
  n : Nat
  m : Multiset Nat
instance : State Conf := ⟨⟩

abbrev Patt (α : Type u) [State α] := α → Prop → Prop
abbrev Rule (α : Type u) [State α] := α → α → Prop → Prop

inductive rule1 : Rule Conf where
  | mk {n : Nat} {m : Multiset Nat} : rule1 ⟨n, m⟩ ⟨n + 1, m⟩ (n < 5)

inductive patt1 : Patt Conf where
  | mk {n : Nat} {m : Multiset Nat} : patt1 ⟨n, m⟩ (n > 3)
#check @patt1.mk

inductive patt2 : Patt Conf where
  | mk {n : Nat} : patt2 ⟨n, ∅⟩ True

/-- Forward application of a rewriting rule to a constrained pattern.
    The result retains both the pattern constraint and the rule guard. -/
def applyRule {α : Type u} [State α]
    (rl : Rule α) (p : Patt α) : Patt α :=
  fun r h =>
    ∃ l pcond rcond,
      p l pcond ∧ rl l r rcond ∧ h = (pcond ∧ rcond)

example :
    applyRule rule1 patt1 ⟨5, ∅⟩ ((4 > 3) ∧ (4 < 5)) := by
  exact ⟨⟨4, ∅⟩, 4 > 3, 4 < 5, patt1.mk, rule1.mk, rfl⟩

#reduce applyRule rule1 patt1

instance {α : Type u} [State α] : Max (Patt α) where
  max p1 p2 := fun st cond => p1 st cond ∨ p2 st cond

#check (patt1 ⊔ patt2)

def Patt.Mem {α : Type u} [State α]
    (s : α) (p : Patt α) : Prop :=
  ∃ cond : Prop, p s cond ∧ cond

instance {α : Type u} [State α] :
    Membership α (Patt α) where
  mem p s := Patt.Mem s p

example : ⟨4, ∅⟩ ∈ patt1 := by
  refine ⟨_, patt1.mk, ?_⟩
  omega

example : ⟨4, ∅⟩ ∈ patt2 := by
  refine ⟨_, patt2.mk, ?_⟩
  trivial

example : ⟨4, ∅⟩ ∈ patt1 ⊔ patt2 := by
  refine ⟨_, Or.inl (patt1.mk), ?_⟩
  omega

example : patt1 ⊔ patt1 = patt1 := by
  funext st cond
  change (patt1 st cond ∨ patt1 st cond) = patt1 st cond
  apply propext
  simp

end old
