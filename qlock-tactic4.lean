/-
Objective: Decoupling unification steps from rest of the proof
& keep the MONOID REPRESENTATION for multisets and lists
-/

import Bakery.DMC3
import Bakery.command

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

import Mathlib.Tactic.IntervalCases


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
    change ¬n + (↑q + {i}) = 0
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



-- MACRO 1: Support Unfolding (Internal Helper)
syntax "unfold_support " ident "[" term,* "]" : tactic
macro_rules
  | `(tactic| unfold_support $id [ $e ]) => `(tactic|
      by_cases $id = $e <;> simp_all)
  | `(tactic| unfold_support $id [ $e, $es,* ]) => `(tactic|
      by_cases $id = $e <;> simp_all <;> unfold_support $id [ $es,* ])

-- MACRO 2: The Backtracking Router (Internal Helper)
syntax "route_and_solve " ident "[" term,* "]" : tactic
macro_rules
  | `(tactic| route_and_solve $id [ $es,* ]) => `(tactic|
      first
        -- Try the left branch, fully solve it, and ensure no goals remain
        | (left; constructor <;> ext $id <;> unfold_support $id [ $es,* ] <;> done)
        -- If left fails, go right and recurse down the Or-tree
        | (right; route_and_solve $id [ $es,* ])
        -- Fallback for the final node (which is no longer an 'Or')
        | (constructor <;> ext $id <;> unfold_support $id [ $es,* ] <;> done)
    )

-- MACRO 3: The Public Unhygienic Combinator
-- Injects the raw 'a' and kicks off the backtracking search.
macro "solve_acu_branch " "[" es:term,* "]" : tactic => do
  let a := Lean.mkIdent `a
  `(tactic| route_and_solve $a [ $es,* ])




lemma completeness_ex1 (X Y : Multiset ℕ) :
  (X + Y = {1} + {2}) →
  (
    (X = {1} + {2} ∧ Y = ∅) ∨
    (X = {1} ∧ Y = {2}) ∨
    (X = {2} ∧ Y = {1}) ∨
    (X = ∅ ∧ Y = {1} + {2})
  ) := by
  intro h

  -- Isolate finite elements to bypass universal quantifier blockage
  have c1 : X.count 1 + Y.count 1 = 1 := by
    have := congr_arg (Multiset.count 1) h
    simp only [Multiset.count_add, Multiset.count_singleton, if_pos] at this
    exact this

  have c2 : X.count 2 + Y.count 2 = 1 := by
    have := congr_arg (Multiset.count 2) h
    simp only [Multiset.count_add, Multiset.count_singleton, if_pos] at this
    exact this

  have c_other : ∀ a, a ≠ 1 → a ≠ 2 → X.count a = 0 ∧ Y.count a = 0 := by
    intro a ha1 ha2
    have := congr_arg (Multiset.count a) h
    simp only [Multiset.count_add, Multiset.count_singleton, if_neg ha1, if_neg ha2] at this
    omega


  -- 2. Generic Integer Bounding
  -- Maude generates bounds for ONE of the variables (e.g., X) based on the RHS counts.
  have b1 : X.count 1 ≤ 1 := by omega
  have b2 : X.count 2 ≤ 1 := by omega

  -- 3. The Automated Terminal Block
  -- interval_cases splits the variables across all valid Diophantine integer states.
  interval_cases h1 : X.count 1 <;>
  interval_cases h2 : X.count 2 <;>
  solve_acu_branch [1, 2]


lemma completeness_ex1' (X Y : Multiset ℕ) :
  (X + Y = {1} + {2}) →
  (
    (X = {1} + {2} ∧ Y = ∅) ∨
    (X = {1} ∧ Y = {2}) ∨
    (X = {2} ∧ Y = {1}) ∨
    (X = ∅ ∧ Y = {1} + {2})
  ) := by
  intro h

  -- Isolate finite elements to bypass universal quantifier blockage
  have c1 : X.count 1 + Y.count 1 = 1 := by
    have := congr_arg (Multiset.count 1) h
    simp only [Multiset.count_add, Multiset.count_singleton, if_pos] at this
    exact this

  have c2 : X.count 2 + Y.count 2 = 1 := by
    have := congr_arg (Multiset.count 2) h
    simp only [Multiset.count_add, Multiset.count_singleton, if_pos] at this
    exact this

  have c_other : ∀ a, a ≠ 1 → a ≠ 2 → X.count a = 0 ∧ Y.count a = 0 := by
    intro a ha1 ha2
    have := congr_arg (Multiset.count a) h
    simp only [Multiset.count_add, Multiset.count_singleton, if_neg ha1, if_neg ha2] at this
    omega

  -- Case-split the quantified-free integer equations
  rcases Nat.add_eq_one_iff.mp c1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩ <;>
  rcases Nat.add_eq_one_iff.mp c2 with ⟨hx2, hy2⟩ | ⟨hx2, hy2⟩

  · right; right; right
    constructor <;> ext a <;> by_cases h1 : a = 1 <;> by_cases h2 : a = 2 <;>
    simp_all
  · right; right; left
    constructor <;> ext a <;> by_cases h1 : a = 1 <;> by_cases h2 : a = 2 <;>
    simp_all
  · right; left
    constructor <;> ext a <;> by_cases h1 : a = 1 <;> by_cases h2 : a = 2 <;>
    simp_all
  · left
    constructor <;> ext a <;> by_cases h1 : a = 1 <;> by_cases h2 : a = 2 <;>
    simp_all
