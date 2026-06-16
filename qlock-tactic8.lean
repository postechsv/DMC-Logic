/-
Objective: constrained ACU unification
-/
import Lean
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Bakery.DMC3

lemma completeness4 (X Y Z : Multiset Nat) :
{1} + Z = X + Y + {2} →
  (∃ U2 U1, X = U2 + {1} ∧ Y = U1 ∧ Z = U1 + U2 + {2}) ∨ ∃ U1 U2, X = U1 ∧ Y = U2 + {1} ∧ Z = U1 + U2 + {2}
  := by
  intro h

  have hc :
      ∀ a : ℕ,
        X.count a + Y.count a + (if a = 2 then 1 else 0)
          =
        (if a = 1 then 1 else 0) + Z.count a := by
    intro a
    have hcnt := congr_arg (fun M : Multiset ℕ => M.count a) h
    simp [Multiset.count_add, Multiset.count_singleton, Multiset.count_cons] at hcnt
    omega

  by_cases hx : 1 ∈ X

  · left

    have hxpos : 0 < X.count 1 := by
      exact Multiset.count_pos.mpr hx

    refine ⟨X.erase 1, Y, ?_, rfl, ?_⟩

    · ext a
      by_cases ha : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hxpos]
        omega
      · simp [Multiset.count_add, Multiset.count_singleton, ha]

    · ext a
      have hca := hc a
      by_cases ha1 : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hxpos] at hca ⊢
        omega
      · by_cases ha2 : a = 2
        · subst a
          have h21 : (2 : ℕ) ≠ 1 := by decide
          simp [Multiset.count_add, Multiset.count_singleton, h21] at hca ⊢
          omega
        · simp [Multiset.count_add, Multiset.count_singleton, ha1, ha2] at hca ⊢
          omega

  · right

    have hx0 : X.count 1 = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hxpos
      exact hx (Multiset.count_pos.mp hxpos)

    have hypos : 0 < Y.count 1 := by
      have hca := hc 1
      simp [Multiset.count_add, Multiset.count_singleton, hx0] at hca
      omega

    refine ⟨X, Y.erase 1, rfl, ?_, ?_⟩

    · ext a
      by_cases ha : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hypos]
        omega
      · simp [Multiset.count_add, Multiset.count_singleton, ha]

    · ext a
      have hca := hc a
      by_cases ha1 : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hx0, hypos] at hca ⊢
        omega
      · by_cases ha2 : a = 2
        · subst a
          have h21 : (2 : ℕ) ≠ 1 := by decide
          simp [Multiset.count_add, Multiset.count_singleton, h21] at hca ⊢
          omega
        · simp [Multiset.count_add, Multiset.count_singleton, ha1, ha2] at hca ⊢
          omega

lemma completeness4_constrained (X Y Z : Multiset ℕ) :
    ({1} + Z = X + Y + {2} ∧ X ≠ ∅ ∧ Y ≠ ∅ ∧ Z ≠ ∅) →
    (
      (∃ U2 U1,
        U1 ≠ ∅ ∧
        X = U2 + {1} ∧
        Y = U1 ∧
        Z = U1 + U2 + {2})
      ∨
      (∃ U1 U2,
        U1 ≠ ∅ ∧
        X = U1 ∧
        Y = U2 + {1} ∧
        Z = U1 + U2 + {2})
    ) := by
  intro h
  rcases h with ⟨h_eq, hXne, hYne, hZne⟩

  have mgu := completeness4 X Y Z h_eq

  rcases mgu with h₁ | h₂
  · left
    rcases h₁ with ⟨U2, U1, hX, hY, hZ⟩
    refine ⟨U2, U1, ?_, hX, hY, hZ⟩
    intro hU1
    apply hYne
    rw [hY, hU1]

  · right
    rcases h₂ with ⟨U1, U2, hX, hY, hZ⟩
    refine ⟨U1, U2, ?_, hX, hY, hZ⟩
    intro hU1
    apply hXne
    rw [hX, hU1]
