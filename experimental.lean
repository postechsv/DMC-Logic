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
