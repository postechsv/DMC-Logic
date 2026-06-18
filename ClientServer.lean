import Bakery.DMC3

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

inductive ClientStatus where
  | idle : ClientStatus
  | crit : ClientStatus

inductive ServerStatus where
  | free : ServerStatus
  | held : Nat → ServerStatus

inductive Proc where
  | c : Nat → ClientStatus → Proc
  | s : ServerStatus → Proc

structure Conf where
  ps : Multiset Proc
instance : State Conf := ⟨⟩

open Conf Proc ServerStatus ClientStatus

inductive enter1 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      enter1 ⟨{c 1 idle} + {s free} + REST⟩ ⟨{c 1 crit} + {s (held 1)} + REST⟩

def enter1_enabled : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{c 1 idle} + {s free} + REST⟩

inductive enter2 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      enter2 ⟨{c 2 idle} + {s free} + REST⟩ ⟨{c 2 crit} + {s (held 2)} + REST⟩

def enter2_enabled : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{c 2 idle} + {s free} + REST⟩

inductive exit1 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      exit1 ⟨{c 1 crit} + {s (held 1)} + REST⟩ ⟨{c 1 idle} + {s free} + REST⟩

def exit1_enabled : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{c 1 crit} + {s (held 1)} + REST⟩

inductive exit2 : Transition Conf where
  | mk : ∀ (REST : Multiset Proc),
      exit2 ⟨{c 2 crit} + {s (held 2)} + REST⟩ ⟨{c 2 idle} + {s free} + REST⟩

def exit2_enabled : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{c 2 crit} + {s (held 2)} + REST⟩

def enabled1 := enter1_enabled ⊔ exit1_enabled
def step1 : Transition Conf := enter1 ⊔ exit1
lemma enabled1_sound :
    ∀ st st', step1 st st' → enabled1 st := by
  intro st st' hstep
  unfold step1 at hstep
  unfold enabled1 enter1_enabled exit1_enabled
  rcases hstep with henter | hexit
  · cases henter with
    | mk REST =>
        left
        exact ⟨REST, rfl⟩
  · cases hexit with
    | mk REST =>
        right
        exact ⟨REST, rfl⟩


def step2 : Transition Conf := enter2 ⊔ exit2
def enabled2 := enter2_enabled ⊔ exit2_enabled
lemma enabled2_sound :
    ∀ st st', step2 st st' → enabled2 st := by
  intro st st' hstep
  unfold step2 at hstep
  unfold enabled2 enter2_enabled exit2_enabled
  rcases hstep with henter | hexit
  · cases henter with
    | mk REST =>
        left
        exact ⟨REST, rfl⟩
  · cases hexit with
    | mk REST =>
        right
        exact ⟨REST, rfl⟩


def allIdle (ps : Multiset Proc) : Prop := ∀p ∈ ps, ∃ I, p = c I idle

-- free phase
def patFree : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{s free} + REST⟩ ∧ allIdle REST

-- critical phase
def patCrit1 : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{s (held 1)} + {c 1 crit} + REST⟩ ∧ allIdle REST

def patCrit2 : Pattern Conf := fun cf =>
  ∃ REST, cf = ⟨{s (held 2)} + {c 2 crit} + REST⟩ ∧ allIdle REST

-- assume conditions
def requires1 : Pattern Conf := fun cf =>
  (∃ REST, cf = ⟨{c 1 idle} + {s free} + REST⟩ ∧ allIdle REST)
  ∨ patCrit1 cf

def requires2 : Pattern Conf := fun cf =>
  (∃ REST, cf = ⟨{c 2 idle} + {s free} + REST⟩ ∧ allIdle REST)
  ∨ patCrit2 cf

-- guarantee conditions
def ensures1 : Pattern Conf := fun cf => patCrit1 cf ∨ patFree cf
def ensures2 : Pattern Conf := fun cf => patCrit2 cf ∨ patFree cf

lemma contract1_enter : (↑enter1 : Transformer Conf) requires1 ensures1 := by sorry
lemma contract1_exit : (↑exit1 : Transformer Conf) requires1 ensures1 := by sorry
lemma contract1 : (↑step1 : Transformer Conf) requires1 ensures1 := by
  unfold step1
  rw [SComp (t1 := enter1)]
  refine ⟨?_, ?_⟩
  · apply contract1_enter
  · apply contract1_exit

lemma contract2_enter : (↑enter2 : Transformer Conf) requires2 ensures2 := by sorry
lemma contract2_exit : (↑exit2 : Transformer Conf) requires2 ensures2 := by sorry
lemma contract2 : (↑step2 : Transformer Conf) requires2 ensures2 := by
  unfold step2
  rw [SComp (t1 := enter2)]
  refine ⟨?_, ?_⟩
  · apply contract2_enter
  · apply contract2_exit

-- {A₁} R₁ {G₁} -- local proof
-- {A₂} R₂ {G₂} -- local proof
-- D₁ ↔ enabled(R₁) -- enabledness
-- D₂ ↔ enabled(R₂) -- enabledness
-- (G₁ ∨ G₂) ∧ D₁ ⊆ A₁ -- compatibility
-- (G₁ ∨ G₂) ∧ D₂ ⊆ A₂ -- compatibility
-- ────────────────────────────
-- {G₁ ∨ G₂} R₁ ∪ R₂ {G₁ ∨ G₂}
lemma PComp {α : Type*} [State α]
    (t1 t2 : Transition α)
    (A1 A2 G1 G2 D1 D2 : Pattern α)
    (h1 : (↑t1 : Transformer α) A1 G1) -- local proof
    (h2 : (↑t2 : Transformer α) A2 G2) -- local proof
    (hD1 : ∀ st st', t1 st st' → D1 st) -- enabledness
    (hD2 : ∀ st st', t2 st st' → D2 st) -- enabledness
    (hC1 : ∀ st, (G1 ⊔ G2) st → D1 st → A1 st) -- compatibility
    (hC2 : ∀ st, (G1 ⊔ G2) st → D2 st → A2 st) -- compatibility
    : (↑(t1 ⊔ t2) : Transformer α) (G1 ⊔ G2) (G1 ⊔ G2) := by
  intro st st' hG hstep
  rcases hstep with hstep1 | hstep2
  · exact Or.inl (h1 st st' (hC1 st hG (hD1 st st' hstep1)) hstep1)
  · exact Or.inr (h2 st st' (hC2 st hG (hD2 st st' hstep2)) hstep2)

def step12 : Transition Conf := step1 ⊔ step2
lemma invariant : (↑step12 : Transformer Conf)
  (ensures1 ⊔ ensures2) (ensures1 ⊔ ensures2) := by
  unfold step12
  apply PComp step1 step2 requires1 requires2 ensures1 ensures2 enabled1 enabled2
  · exact contract1
  · exact contract2
  · exact enabled1_sound
  · exact enabled2_sound
  · exact sorry --- (compatibility)
  · exact sorry --- (compatibility)
