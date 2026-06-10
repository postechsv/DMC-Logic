/-
Objective: Decoupling unification steps from rest of the proof
& keep the MONOID REPRESENTATION for multisets and lists
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
      step_n2w ⟨ {i} + n, w, c, q ⟩ ⟨ n, {i} + w, c, q ++ [i] ⟩


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
  POSITIVE CASE: unifiable
-/

-- unification proof
instance {N N' W' C' : Multiset ℕ} {Q Q' : List ℕ} {i : Nat} :
  Unify
    { n := {i} + N', w := W', c := C', q := Q' }
    { n := N, w := ↑Q, c := 0, q := Q }
    (({i} + N' = N) ∧ (W' = ↑Q) ∧ (C' = 0) ∧ (Q' = Q)) where
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
  rename_i i n w c q
  obtain ⟨h_n, h_w, h_c, h_q⟩ := unifier

  /- rest of the proof: constraint solving w.r.t. unifier -/
  simp [pat1, -Multiset.singleton_add] -- prevent ::ₘ from appearing
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩

  · -- {i} + w = ↑(q ++ [i])
    change {i} + w = ↑q + {i}
    rw [h_w, h_q, Multiset.add_comm ↑Q {i}]
  · -- c = 0
    assumption
  · -- ¬n + ↑(q ++ [i]) = 0
    -- observation: h_s1 and current goal matches up to h_n & h_q
    -- idea: using Maude as a quick hint oracle?
    rw [← Multiset.coe_add]; change ¬n + (↑q + {i}) = 0
    intro h_contra
    apply h_s1
    rw [← h_n, ← h_q, Multiset.add_comm {i} n, Multiset.add_assoc, Multiset.add_comm {i} ↑q]
    assumption
  · -- (n + ↑(q ++ [i])).Nodup
    -- observation: h_s2 and current goal matches up to h_n & h_q
    -- idea: using Maude as a quick hint oracle?
    change (n + (↑q + {i})).Nodup
    rw [
      Multiset.add_comm ↑q {i},  -- Goal becomes: (n + ({i} + ↑q)).Nodup
      ← Multiset.add_assoc,      -- Goal becomes: ((n + {i}) + ↑q).Nodup
      Multiset.add_comm n {i},   -- Goal becomes: (({i} + n) + ↑q).Nodup
      h_n,                       -- Goal becomes: (N + ↑q).Nodup
      h_q                        -- Goal becomes: (N + ↑Q).Nodup
    ]
    exact h_s2

end ex1
