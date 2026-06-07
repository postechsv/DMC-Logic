import Bakery.DMC3
import Bakery.command


import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

import Lean
import Qq

open Lean Meta Elab Tactic



structure Conf where
  n : Multiset Nat
  w : Multiset Nat
  c : Multiset Nat
  q : List Nat

structure Conf' where
  n : Multiset Nat
  w : Multiset Nat
  q : List Nat
  c : Multiset Nat

instance : State Conf := ⟨⟩
instance : State Conf' := ⟨⟩

inductive step_n2w : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_n2w ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

inductive step_w2c : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_w2c ⟨ n, i ::ₘ w, c, i :: q ⟩ ⟨ n, w, i ::ₘ c, i :: q ⟩

inductive step_c2n : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_c2n ⟨ n, w, i ::ₘ c, i :: q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

inductive step_c2n' : Transition Conf' where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_c2n' ⟨ n, w, i :: q, i ::ₘ c ⟩ ⟨ i ::ₘ n, w, q, c ⟩




/- pat1
  (< U:MSet | W:MSet | mt | Q:List >) s.t.
    (non-mt(U:MSet W:MSet) = tt)
    /\ (set(U:MSet W:MSet) = tt)
    /\ (l2ms(Q:List) = W:MSet))
-/
def pat1 : Pattern Conf := fun cf =>
  ∃ (U W : Multiset Nat) (Q : List Nat),
    cf = ⟨ U, W, ∅, Q ⟩
    ∧ U + W ≠ ∅
    ∧ Multiset.Nodup (U + W)
    ∧ ↑Q = W

def pat1' : Pattern Conf' := fun cf =>
  ∃ (U W : Multiset Nat) (Q : List Nat),
    cf = ⟨ U, W, Q, ∅ ⟩
    ∧ U + W ≠ ∅
    ∧ Multiset.Nodup (U + W)
    ∧ ↑Q = W

/- pred2
  (< V:MSet | T:MSet | i:Nat | i:Nat ; Q':List >) s.t.
    (non-mt(V:MSet T:MSet i:Nat) = tt)
    /\ (set(V:MSet T:MSet i:Nat) = tt)
    /\ (l2ms(i:Nat ; Q':List) = T:MSet i:Nat))
-/
def pat2 : Pattern Conf := fun cf =>
  ∃ (i : Nat) (V T : Multiset Nat) (Q' : List Nat),
    cf = ⟨ V, T, {i}, i :: Q' ⟩
    ∧ V + T + {i} ≠ ∅
    ∧ Multiset.Nodup (V + T + {i})
    ∧ ↑(i :: Q') = i ::ₘ T





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
macro "destruct_step " step:ident unify:ident : tactic =>
  `(tactic| try {
    rcases $step:ident
    injection $unify:ident
    simp_all
    done
  })

-- ∀ st st', pat1 st → step_c2n st st' → ⊥ st'
lemma _1c0 : (↑step_c2n : Transformer Conf) pat1 ⊥ := by
  intro s s' h_s step
  simp [pat1] at h_s
  obtain ⟨N, Q, h_unify, h_s1, h_s2⟩ := h_s

  -- current proof state:
  --   ...
  --   h_unify : s = { n := N, w := ↑Q, c := 0, q := Q }
  --   ⊢ ⊥ s'

  destruct_step step h_unify -- this line covers the following 3 lines commented proof:
  -- cases step -- { n := n✝, w := w✝, c := i✝ ::ₘ c✝, q := i✝ :: q✝ } = { n := N, w := ↑Q, c := 0, q := Q }
  -- injection h_unify with _ _ hc _ -- hc : i✝ ::ₘ c✝ = 0
  -- simp at hc -- contradiction found: 0 cannot be of the form i✝ ::ₘ c✝


-- variant of _1c0 for Conf'
lemma _1c0' : (↑step_c2n' : Transformer Conf') pat1' ⊥ := by
  intro s s' h_s step
  simp [pat1'] at h_s
  obtain ⟨N, Q, h_unify, h_s1, h_s2⟩ := h_s
  destruct_step step h_unify




-- ∀ st st', pat1 st → step_n2w st st' → pat1 st'
lemma _1a1 : (↑step_n2w : Transformer Conf) pat1 pat1 := by
  intro s s' ps step
  simp [pat1] at ps
  obtain ⟨N, Q, h_unify, h_s1, h_s2⟩ := ps
  destruct_step step h_unify -- does nothing because h_unify is unifiable

  cases step
  --rcases step with ⟨i, N', W', C', Q'⟩
  simp [pat1]
  refine ⟨?_, ?_, ?_⟩

  · sorry
  · sorry
  · sorry

lemma _1b2 : (↑step_w2c : Transformer Conf) pat1 pat2 := sorry
lemma _2a2 : (↑step_n2w : Transformer Conf) pat2 pat2 := sorry
lemma _2b0 : (↑step_w2c : Transformer Conf) pat2 ⊥ := sorry
lemma _2c1 : (↑step_c2n : Transformer Conf) pat2 pat1 := sorry
