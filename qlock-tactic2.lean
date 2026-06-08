/-
Objective: automate the process of pruning non-unifiable cases with tactics
-/

import Bakery.DMC3
import Bakery.command

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

import Lean
import Qq

open Lean Meta Elab Tactic

/- TODO
* get rid of inductive types for steps and keep it simple
* AC matching
-/

-- attempt 1: hardcoded version for _1c0
-- macro "destruct_step" step:ident unify:ident : tactic => `(tactic|
--   (cases $step:ident
--    first | injection $unify:ident with _ _ hc _ | injection $unify:ident
--    simp at hc))

-- attempt 2
-- macro "destruct_step " step:ident unify:ident : tactic =>
--   `(tactic| {
--     rcases $step:ident
--     injection $unify:ident
--     simp_all
--   })

-- attempt 3: rollback
-- macro "destruct_step " step:ident unify:ident : tactic =>
--   `(tactic| try {
--     rcases $step:ident
--     injection $unify:ident
--     simp_all
--     done
--   })

-- attempt 4: handle ::ₘ for multisets
macro "destruct_step " step:ident unify:ident : tactic =>
  `(tactic| try {
    rcases $step:ident
    injection $unify:ident
    simp_all [Multiset.cons_eq_cons]
    done
  })


/- EXAMPLE 1 -/
namespace ex1

structure Conf where
  n : Multiset Nat
  w : Multiset Nat
  c : Multiset Nat
  q : List Nat
instance : State Conf := ⟨⟩


inductive step_c2n : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_c2n ⟨ n, w, i ::ₘ c, i :: q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

def pat1 : Pattern Conf := fun cf =>
  ∃ (U W : Multiset Nat) (Q : List Nat),
    cf = ⟨ U, W, ∅, Q ⟩
    ∧ U + W ≠ ∅
    ∧ Multiset.Nodup (U + W)
    ∧ ↑Q = W

/- NEGATIVE CASE -/
-- ∀ st st', pat1 st → step_c2n st st' → ⊥ st'
lemma _1c0 : (↑step_c2n : Transformer Conf) pat1 ⊥ := by
  intro s s' h_s step
  simp [pat1] at h_s
  obtain ⟨N, Q, h_unify, h_s1, h_s2⟩ := h_s

  destruct_step step h_unify -- this line covers the following 3 lines commented proof:
  -- cases step -- { n := n✝, w := w✝, c := i✝ ::ₘ c✝, q := i✝ :: q✝ } = { n := N, w := ↑Q, c := 0, q := Q }
  -- injection h_unify with _ _ hc _ -- hc : i✝ ::ₘ c✝ = 0
  -- simp at hc -- contradiction found: 0 cannot be of the form i✝ ::ₘ c✝

end ex1


/- EXAMPLE 2 -/
namespace ex2

structure Conf where
  n : Multiset Nat
  w : Multiset Nat
  q : List Nat /- CHANGE: q comes before c -/
  c : Multiset Nat
instance : State Conf := ⟨⟩

inductive step_c2n : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_c2n ⟨ n, w, i :: q, i ::ₘ c ⟩ ⟨ i ::ₘ n, w, q, c ⟩

def pat1 : Pattern Conf := fun cf =>
  ∃ (U W : Multiset Nat) (Q : List Nat),
    cf = ⟨ U, W, Q, ∅ ⟩
    ∧ U + W ≠ ∅
    ∧ Multiset.Nodup (U + W)
    ∧ ↑Q = W

lemma _1c0 : (↑step_c2n : Transformer Conf) pat1 ⊥ := by
  intro s s' h_s step
  simp [pat1] at h_s
  obtain ⟨N, Q, h_unify, h_s1, h_s2⟩ := h_s
  destruct_step step h_unify /- destruct_step still applies despite the change! -/

end ex2



/- EXAMPLE 3 -/
namespace ex3

structure Conf where
  numbers : List Nat
  counter : Nat
instance : State Conf := ⟨⟩

inductive count3 : Transition Conf where
  | mk : ∀ (L : List Nat) (N : Nat), count3 ⟨ 3 :: L, N ⟩ ⟨ L, N + 1 ⟩

def pat : Pattern Conf := fun cf =>
  ∃ (n N : Nat), cf = ⟨ [1,n] , N ⟩

example : (↑count3 : Transformer Conf) pat ⊥ := by
  intro s s' h_s step
  simp [pat] at h_s
  obtain ⟨n, N, h_unify⟩ := h_s

  cases step
  injection h_unify with h1 h2 -- h1 : 3 :: L✝ = [1, n]
  simp at h1
  -- the above three lines can be replaced by the following
  -- destruct_step step h_unify

end ex3

/- EXAMPLE 4 -/
namespace ex4

structure Conf where
  numbers : Multiset Nat
  counter : Nat
instance : State Conf := ⟨⟩

inductive count3 : Transition Conf where
  | mk : ∀ (MS : Multiset Nat) (N : Nat), count3 ⟨ 3 ::ₘ MS, N ⟩ ⟨ MS, N + 1 ⟩

def pat : Pattern Conf := fun cf =>
  ∃ (N : Nat), cf = ⟨ {1,2} , N ⟩

example : (↑count3 : Transformer Conf) pat ⊥ := by
  intro s s' h_s step
  simp [pat] at h_s
  obtain ⟨N, h_unify⟩ := h_s
  destruct_step step h_unify /- it works! -/
  -- destruct_step effectively performs:
  --   cases step
  --   injection h_unify with h1 h2
  --   simp [Multiset.cons_eq_cons] at h1

end ex4


/- TODO: continue examples with AC unification -/
namespace ex5

structure Conf where
  numbers : Multiset Nat
  counter : Nat
instance : State Conf := ⟨⟩

inductive halve : Transition Conf where
  | mk : ∀ (MS : Multiset Nat) (N : Nat), halve ⟨ MS + MS, N ⟩ ⟨ MS, N + 1 ⟩

def pat : Pattern Conf := fun cf =>
  ∃ (N : Nat), cf = ⟨ {1,2,3} , N ⟩

example : (↑halve : Transformer Conf) pat ⊥ := by
  intro s s' h_s step
  simp [pat] at h_s
  obtain ⟨N, h_unify⟩ := h_s
  -- destruct_step step h_unify
  -- destruct_step effectively performs:
  cases step
  injection h_unify with h1 h2 -- h1 : MS✝ + MS✝ = 1 ::ₘ 2 ::ₘ {3}
  simp [Multiset.cons_eq_cons, add_assoc, add_comm, add_left_comm] at h1 -- what should i add?

end ex5

namespace ex6

structure Conf where
  val : Multiset Nat
instance : State Conf := ⟨⟩

-- Rule: Requires a frame (X), plus exactly TWO {1} tokens.
inductive dedupl : Transition Conf where
  | mk : ∀ (X : Multiset Nat), dedupl ⟨ X + {1} + {1} ⟩ ⟨ ∅ ⟩

-- Pattern: The state is strictly exactly ONE {1} token.
def pat : Pattern Conf := fun cf =>
  cf = ⟨ {1} ⟩

end ex6
