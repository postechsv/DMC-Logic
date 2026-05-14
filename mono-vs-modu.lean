import Bakery.DMC3

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub




structure Conf where
  n : Multiset Nat
  w : Multiset Nat
  c : Multiset Nat
  q : List Nat

instance : State Conf := ⟨⟩


-- ==========================================
--        Monolithic Approach
-- ==========================================
inductive MonolithicStep : Transition Conf where
  -- n2w:    ⟨ n i | w | c | q ⟩     →    ⟨ n | w i | c | q ; i ⟩
  | n2w : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      MonolithicStep
        ⟨ i ::ₘ n, w, c, q ⟩
        ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

  -- w2c:  ⟨ n | w i | c | i ; q ⟩   →    ⟨ n | w | c i | i ; q ⟩
  | w2c : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      MonolithicStep ⟨ n, i ::ₘ w, c, i :: q ⟩ ⟨ n, w, i ::ₘ c, i :: q ⟩



-- ==========================================
--          Modular Approach
-- ==========================================
inductive step_n2w : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_n2w ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

inductive step_w2c : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_w2c ⟨ n, i ::ₘ w, c, i :: q ⟩ ⟨ n, w, i ::ₘ c, i :: q ⟩

def ModularStep : Transition Conf :=
  step_n2w ⊔ step_w2c



-- ==========================================
--          Monolithic = Modular
-- ==========================================
theorem equivalence : MonolithicStep = ModularStep := by
  -- Step A: Function & Propositional Extensionality
  -- "Two relations are equal if they logically imply each other for all states"
  ext st st'

  -- Step B: Split the equality into a forward (→) and backward (←) proof
  constructor

  -- ==========================================
  -- DIRECTION 1: Monolithic → Modular
  -- ==========================================
  · intro h_mono
    -- `cases` shatters the monolithic step into its individual constructors
    cases h_mono

    -- Case 1: The transition was n2w
    -- (We use `left` to pick the left side of the `⊔` / `∨`)
    case n2w i n w c q =>
      left
      exact step_n2w.mk i n w c q

    -- Case 2: The transition was w2c
    -- (We use `right` to pick the right side of the `⊔` / `∨`)
    case w2c i n w c q =>
      right
      exact step_w2c.mk i n w c q

  -- ==========================================
  -- DIRECTION 2: Modular → Monolithic
  -- ==========================================
  · intro h_mod
    -- `rcases` is a super-powered `cases` that automatically unpacks
    -- the chain of logical ORs (⊔) into separate branches!
    rcases h_mod with (h_n2w | h_w2c)

    -- Branch 1: It came from the modular step_n2w
    · cases h_n2w
      -- Lean automatically figures out the variables, so we just apply the monolithic constructor
      exact MonolithicStep.n2w _ _ _ _ _

    -- Branch 2: It came from the modular step_w2c
    · cases h_w2c
      exact MonolithicStep.w2c _ _ _ _ _
