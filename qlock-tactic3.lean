/-
Objective: Decoupling unification steps from rest of the proof
-/

import Bakery.DMC3
import Bakery.command

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub



/- EXAMPLE 1 -/
namespace ex1

structure Conf where
  n : Multiset Nat
  w : Multiset Nat
  c : Multiset Nat
  q : List Nat
instance : State Conf := ⟨⟩


inductive step_n2w : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_n2w ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

inductive step_c2n : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_c2n ⟨ n, w, i ::ₘ c, i :: q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

def pat1 : Pattern Conf := fun cf =>
  ∃ (U W : Multiset Nat) (Q : List Nat),
    cf = ⟨ U, W, ∅, Q ⟩
    ∧ U + W ≠ ∅
    ∧ Multiset.Nodup (U + W)
    ∧ ↑Q = W


-- Generic Adapter: uses outParam to represent the unifier (positive case) / ⊥ (negative case)
class Unify (c1 c2 : Conf) (Result : outParam Prop) where
  resolve : c1 = c2 → Result




/-
  NEGATIVE CASE: non-unifiable
-/

-- unification proof
instance {N N' W' C' : Multiset ℕ} {Q Q' : List ℕ} {i : Nat} :
  Unify
    { n := N', w := W', c := i ::ₘ C', q := i :: Q' }
    { n := N, w := ↑Q, c := 0, q := Q }
    False where
  resolve h_unify := by
    injection h_unify; simp_all

-- ∀ st st', pat1 st → step_c2n st st' → ⊥ st'
lemma _1c0 : (↑step_c2n : Transformer Conf) pat1 ⊥ := by
  -- boilerplate: unpacking the pattern and the step
  intro s s' h_s step
  simp [pat1] at h_s
  obtain ⟨N, Q, h_unify, h_s1, h_s2⟩ := h_s
  rcases step

  -- { n := n✝, w := w✝, c := i✝ ::ₘ c✝, q := i✝ :: q✝ } = { n := N, w := ↑Q, c := 0, q := Q }
  obtain unifier := Unify.resolve h_unify

  /- the unifier returned false, so complete the proof -/
  assumption






/-
  POSITIVE CASE: unifiable
-/

-- unification proof
instance {N N' W' C' : Multiset ℕ} {Q Q' : List ℕ} {i : Nat} :
  Unify
    { n := i ::ₘ N', w := W', c := C', q := Q' }
    { n := N, w := ↑Q, c := 0, q := Q }
    ((i ::ₘ N' = N) ∧ (W' = ↑Q) ∧ (C' = 0) ∧ (Q' = Q)) where
  resolve h_unify := by
    injection h_unify with hn hw hc hq
    exact ⟨hn, hw, hc, hq⟩



-- ∀ st st', pat1 st → step_n2w st st' → pat1 st'
lemma _1a1 : (↑step_n2w : Transformer Conf) pat1 pat1 := by
  -- boilerplate: unpacking the pattern and the step
  intro s s' ps step
  simp [pat1] at ps
  obtain ⟨N, Q, h_unify, h_s1, h_s2⟩ := ps
  rcases step

  -- { n := i✝ ::ₘ n✝, w := w✝, c := c✝, q := q✝ } = { n := N, w := ↑Q, c := 0, q := Q }
  obtain unifier := Unify.resolve h_unify

  /- unifier exists, so unpack the bindings -/
  obtain ⟨h_n, h_w, h_c, h_q⟩ := unifier

  /- rest of the proof: constraint solving w.r.t. unifier -/
  rename_i i n w c q
  simp [pat1]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩

  · -- i ::ₘ w = ↑(q ++ [i])
    simp [h_w, h_q]
    exact (List.perm_append_singleton _ Q).symm
  · -- c = 0
    assumption
  · -- ¬n + ↑(q ++ [i]) = 0
    intro h_contra
    apply h_s1
    calc N + ↑Q
        = (i ::ₘ n) + ↑q                    := by rw [← h_n, ← h_q]
      _ = ({i} + n) + ↑q                    := by rw [← Multiset.singleton_add]
      _ = n + {i} + ↑q                      := by rw [Multiset.add_comm {i}, Multiset.add_assoc]
      _ = n + ({i} + ↑q)                    := by rw [← Multiset.add_assoc]
      _ = n + ↑([i] ++ q)                   := by rw [← Multiset.coe_add]; rfl
      _ = n + ↑(q ++ [i])                   := by
        apply congr_arg (fun x => n + x)
        rw [Multiset.coe_eq_coe]
        exact (List.perm_append_singleton i q).symm
      _ = 0                                     := h_contra
  · -- (n + ↑(q ++ [i])).Nodup
    have h_eq : N + ↑Q = n + ↑(q ++ [i]) := by
      calc N + ↑Q
        _ = (i ::ₘ n) + ↑q      := by rw [← h_n, ← h_q]
        _ = ({i} + n) + ↑q      := by rw [← Multiset.singleton_add]
        _ = (n + {i}) + ↑q      := by rw [Multiset.add_comm {i} n]
        _ = n + ({i} + ↑q)      := by rw [Multiset.add_assoc]
        _ = n + ↑([i] ++ q)     := by rw [← Multiset.coe_add]; rfl
        _ = n + ↑(q ++ [i])     := by
          apply congr_arg (fun x => n + x)
          rw [Multiset.coe_eq_coe]
          exact (List.perm_append_singleton i q).symm
    rw [h_eq] at h_s2
    exact h_s2

end ex1
