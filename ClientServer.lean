import Bakery.DMC3

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

inductive ClientStatus where
  | idle : ClientStatus
  | crit : ClientStatus

inductive ServerStatus where
  | free : Nat → ServerStatus
  | held : Nat → ServerStatus

inductive Proc where
  | c : Nat → ClientStatus → Proc
  | s : ServerStatus → Proc

structure Conf where
  ps : Multiset Proc
instance : State Conf := ⟨⟩

open Conf Proc ServerStatus ClientStatus

-- alternating ticket: free 1 → held 1 → free 2 → held 2 → free 1

inductive enter1 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      enter1 ⟨{c 1 idle} + {s (free 1)} + REST⟩ ⟨{c 1 crit} + {s (held 1)} + REST⟩


inductive enter2 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      enter2 ⟨{c 2 idle} + {s (free 2)} + REST⟩ ⟨{c 2 crit} + {s (held 2)} + REST⟩


inductive exit1 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      exit1 ⟨{c 1 crit} + {s (held 1)} + REST⟩ ⟨{c 1 idle} + {s (free 2)} + REST⟩

inductive exit2 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      exit2 ⟨{c 2 crit} + {s (held 2)} + REST⟩ ⟨{c 2 idle} + {s (free 1)} + REST⟩


/- Defining state predicates (Note the allIdle constraint on environment) -/
def allIdle (ps : Multiset Proc) : Prop := ∀p ∈ ps, ∃ I, p = c I idle

def patFree1 : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{s (free 1)} + REST⟩ ∧ allIdle REST

def patFree2 : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{s (free 2)} + REST⟩ ∧ allIdle REST

def patCrit1 : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{s (held 1)} + {c 1 crit} + REST⟩ ∧ allIdle REST

def patCrit2 : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{s (held 2)} + {c 2 crit} + REST⟩ ∧ allIdle REST


/- Establishing contract for client 1 -/
def requires1 := patFree1 ⊔ patCrit1
def ensures1 := patFree2 ⊔ patCrit1

lemma contract1_enter : (↑enter1 : Transformer Conf) requires1 ensures1 := by sorry
lemma contract1_exit : (↑exit1 : Transformer Conf) requires1 ensures1 := by sorry

def step1 : Transition Conf := enter1 ⊔ exit1
lemma contract1 : (↑step1 : Transformer Conf) requires1 ensures1 := by
  unfold step1
  rw [SComp (t1 := enter1)]
  refine ⟨?_, ?_⟩
  · apply contract1_enter
  · apply contract1_exit



/- Establishing contract for client 2 -/
def requires2 := patFree2 ⊔ patCrit2
def ensures2 := patFree1 ⊔ patCrit2

lemma contract2_enter : (↑enter2 : Transformer Conf) requires2 ensures2 := by sorry
lemma contract2_exit : (↑exit2 : Transformer Conf) requires2 ensures2 := by sorry

def step2 : Transition Conf := enter2 ⊔ exit2
lemma contract2 : (↑step2 : Transformer Conf) requires2 ensures2 := by
  unfold step2
  rw [SComp (t1 := enter2)]
  refine ⟨?_, ?_⟩
  · apply contract2_enter
  · apply contract2_exit



/- Compositional Verification using PComp -/
def Enabled {α : Type*} [State α] (t : Transition α) : Pattern α :=
  fun st => ∃ st', t st st'

-- {A₁} R₁ {G₁} -- local proof
-- {A₂} R₂ {G₂} -- local proof
-- (G₁ ∨ G₂) ∧ Enabled(R₁) ⊆ A₁ -- compatibility
-- (G₁ ∨ G₂) ∧ Enabled(R₂) ⊆ A₂ -- compatibility
-- ──────────────────────────── (PComp)
-- {G₁ ∨ G₂} R₁ ∪ R₂ {G₁ ∨ G₂}
lemma PComp {α : Type*} [State α]
    (t1 t2 : Transition α)
    (A1 A2 G1 G2 : Pattern α)
    (h1 : (↑t1 : Transformer α) A1 G1) -- local proof
    (h2 : (↑t2 : Transformer α) A2 G2) -- local proof
    (hC1 : ∀ st, (G1 ⊔ G2) st → Enabled t1 st → A1 st) -- compatibility
    (hC2 : ∀ st, (G1 ⊔ G2) st → Enabled t2 st → A2 st) -- compatibility
    : (↑(t1 ⊔ t2) : Transformer α) (G1 ⊔ G2) (G1 ⊔ G2) := by
  intro st st' hG hstep
  rcases hstep with hstep1 | hstep2
  · exact Or.inl (h1 st st' (hC1 st hG ⟨st', hstep1⟩) hstep1)
  · exact Or.inr (h2 st st' (hC2 st hG ⟨st', hstep2⟩) hstep2)

def step12 : Transition Conf := step1 ⊔ step2
lemma invariant : (↑step12 : Transformer Conf)
  (ensures1 ⊔ ensures2) (ensures1 ⊔ ensures2) := by
  unfold step12
  apply PComp step1 step2 requires1 requires2 ensures1 ensures2
  · exact contract1
  · exact contract2
  · exact sorry --- (compatibility)
  · exact sorry --- (compatibility)
