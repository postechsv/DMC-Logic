import Bakery.DMC3

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub


structure Conf where
  n : Multiset Nat
  w : Multiset Nat
  c : Multiset Nat
  q : List Nat

instance : State Conf := ⟨⟩


/-
inductive Step : Transition Conf where
  -- n2w:    ⟨ n i | w | c | q ⟩     →    ⟨ n | w i | c | q ; i ⟩
  | n2w : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step
        ⟨ i ::ₘ n, w, c, q ⟩
        ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

  -- w2c:  ⟨ n | w i | c | i ; q ⟩   →    ⟨ n | w | c i | i ; q ⟩
  | w2c : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step ⟨ n, i ::ₘ w, c, i :: q ⟩ ⟨ n, w, i ::ₘ c, i :: q ⟩

  -- c2n:  ⟨ n | w | c i | i ; q ⟩   →    ⟨ n i | w | c | q ⟩
  | c2n : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step ⟨ n, w, i ::ₘ c, i :: q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

  -- **join**:   ⟨ n | w | c | q ⟩       →    ⟨ n **i** | w | c | q ⟩  if ¬ dupl(n i w c)
  | join : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      (i ∉ n + w + c) →
      Step ⟨ n, w, c, q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

  -- exit:   ⟨ n i | w | c | q ⟩     →    ⟨ n | w | c | q ⟩
  | exit : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, w, c, q ⟩
-/

inductive step_n2w : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_n2w ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

inductive step_w2c : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_w2c ⟨ n, i ::ₘ w, c, i :: q ⟩ ⟨ n, w, i ::ₘ c, i :: q ⟩

inductive step_c2n : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_c2n ⟨ n, w, i ::ₘ c, i :: q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

inductive step_join : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      (i ∉ n + w + c) →
      step_join ⟨ n, w, c, q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

inductive step_exit : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_exit ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, w, c, q ⟩


def Step : Transition Conf :=
  step_n2w ⊔ step_w2c ⊔ step_c2n ⊔ step_join ⊔ step_exit




def init : Pattern Conf := fun cf =>
  ∃ (i : Nat) (S : Multiset Nat),
    cf = ⟨ i ::ₘ S, ∅, ∅, List.nil ⟩
    ∧ Multiset.Nodup (i ::ₘ S)

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

def inv := pat1 ⊔ pat2

#check (init : Pattern Conf) -- Conf → Prop
#check (pat1 : Pattern Conf) -- Conf → Prop
#check (pat2 : Pattern Conf) -- Conf → Prop
#check (pat1 ⊔ pat2 : Pattern Conf) -- Conf → Prop


lemma inv_ind : (↑Step : Transformer Conf) (pat1 ⊔ pat2) (pat1 ⊔ pat2) := sorry
lemma inv_init : (↑Step : Transformer Conf) init (pat1 ⊔ pat2) := sorry

-- ⟨ 1 ::ₘ 0 , ∅, ∅, List.nil ⟩ => ⟨ {0}, {1}, ∅, [1] ⟩
def cf0 (cf : Conf) : Prop := cf = ⟨ 1 ::ₘ 0 , ∅, ∅, List.nil ⟩
def cf1 (cf : Conf) : Prop := cf = ⟨ {0}, {1}, ∅, [1] ⟩
