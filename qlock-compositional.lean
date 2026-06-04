import Bakery.DMC3
import Bakery.command


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
  step_n2w ⊔ step_w2c ⊔ step_c2n

def Step' : Transition Conf :=
  step_n2w ⊔ step_w2c ⊔ step_c2n ⊔ step_join ⊔ step_exit

#print_steps Step
-- Transition 'Step' is composed of:
--   step_n2w
--   step_w2c
--   step_c2n
--   step_join
--   step_exit

def init : Pattern Conf := fun cf =>
  ∃ (i : Nat) (S : Multiset Nat),
    cf = ⟨ i ::ₘ S, ∅, ∅, List.nil ⟩
    ∧ Multiset.Nodup (i ::ₘ S)

#apply_steps Step on init

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


lemma _1a1 : (↑step_n2w : Transformer Conf) pat1 pat1 := by
  intro s s' ps step

  simp [pat1] at ps
  obtain ⟨N, Q, rfl, h_s1, h_s2⟩ := ps

  rcases step with ⟨i, N', W', C', Q'⟩

  simp [pat1]
  refine ⟨?_, ?_, ?_⟩

  · sorry
  · sorry
  · sorry
lemma _1b2 : (↑step_w2c : Transformer Conf) pat1 pat2 := sorry
lemma _1c0 : (↑step_c2n : Transformer Conf) pat1 ⊥ := sorry
lemma _2a2 : (↑step_n2w : Transformer Conf) pat2 pat2 := sorry
lemma _2b0 : (↑step_w2c : Transformer Conf) pat2 ⊥ := sorry
lemma _2c1 : (↑step_c2n : Transformer Conf) pat2 pat1 := sorry

lemma _1a12 : (↑step_n2w : Transformer Conf) pat1 (pat1 ⊔ pat2) := by
  apply RComp' (p' := pat1)
  · apply _1a1
  · apply le_sup_left

lemma _1b12 : (↑step_w2c : Transformer Conf) pat1 (pat1 ⊔ pat2) := by
  apply RComp' (p' := pat2)
  · apply _1b2
  · apply le_sup_right

lemma _1c12 : (↑step_c2n : Transformer Conf) pat1 (pat1 ⊔ pat2) := by
  apply RComp' (p' := ⊥)
  · apply _1c0
  · apply bot_le

lemma _2a12 : (↑step_n2w : Transformer Conf) pat2 (pat1 ⊔ pat2) := by
  apply RComp' (p' := pat2)
  · apply _2a2
  · apply le_sup_right

lemma _2b12 : (↑step_w2c : Transformer Conf) pat2 (pat1 ⊔ pat2) := by
  apply RComp' (p' := ⊥)
  · apply _2b0
  · apply bot_le

lemma _2c12 : (↑step_c2n : Transformer Conf) pat2 (pat1 ⊔ pat2) := by
  apply RComp' (p' := pat1)
  · apply _2c1
  · apply le_sup_left

-- step_n2w ⊔ step_w2c ⊔ step_c2n
lemma _1abc12 : (↑Step : Transformer Conf) pat1 (pat1 ⊔ pat2) := by
  unfold Step -- [Step]
  rw [SComp (t1 := step_n2w ⊔ step_w2c)]
  rw [SComp (t1 := step_n2w)]
  refine ⟨⟨?_,?_⟩,?_⟩ -- fixme: ⊔ is left-associative unlike ∧
  · apply _1a12
  · apply _1b12
  · apply _1c12

lemma _2abc12 : (↑Step : Transformer Conf) pat2 (pat1 ⊔ pat2) := by
  unfold Step -- [Step]
  rw [SComp (t1 := step_n2w ⊔ step_w2c)]
  rw [SComp (t1 := step_n2w)]
  refine ⟨⟨?_,?_⟩,?_⟩ -- fixme: ⊔ is left-associative unlike ∧
  · apply _2a12
  · apply _2b12
  · apply _2c12

lemma _12abc12 : (↑Step : Transformer Conf) (pat1 ⊔ pat2) (pat1 ⊔ pat2) := by
  rw [LComp]; refine ⟨?_,?_⟩
  · apply _1abc12
  · apply _2abc12


def inv_ind : (↑Step : Transformer Conf) (pat1 ⊔ pat2) (pat1 ⊔ pat2) := _12abc12
/-
1a1: pat1 --(n2w)--> pat1
1b2: pat1 --(w2c)--> pat2
1c0: pat1 --(c2n)--> ⊥ (empty pattern)
1d1: pat1 --(join)--> pat1
1e1: pat1 --(exit)--> pat1

2a2: pat2 --(n2w)--> pat2
2b0: pat2 --(w2c)--> ⊥ (empty pattern)
2c1: pat2 --(c2n)--> pat1
2d2: pat2 --(join)--> pat2
2e2: pat2 --(exit)--> pat2
-/

/- Proof Composition

    1a1          1b2          1c0              2a2          2b0          2c1
    ----(RComp)  ----(RComp)  ----(RComp)      ----(RComp)  ----(RComp)  ----(RComp)
    1a12         1b12         1c12             2a12         2b12         2c12
  ----------------------------------(SComp)  ----------------------------------(SComp)
                1abc12                                      2abc12
---------------------------------------------------------------------------------------(LComp)
                                      12abc12

     (...)    (++)
    -------  ------
    12abc12  12de12
  -------------------(SComp)
       12abcde12
-/
lemma inv_init : (↑Step : Transformer Conf) init (pat1 ⊔ pat2) := sorry

-- ⟨ 1 ::ₘ 0 , ∅, ∅, List.nil ⟩ => ⟨ {0}, {1}, ∅, [1] ⟩
def cf0 (cf : Conf) : Prop := cf = ⟨ 1 ::ₘ 0 , ∅, ∅, List.nil ⟩
def cf1 (cf : Conf) : Prop := cf = ⟨ {0}, {1}, ∅, [1] ⟩




--- some experiments with gemini
example (st next_st : Conf) (h_init : init st) (h_step : step_n2w st next_st) : True := by

  -- 1. SHATTER THE TRANSITION FIRST!
  -- Because `st` is just a free variable right now, Lean doesn't have to guess.
  -- It just assigns internal variables to everything.
  cases h_step

  -- [CLICK HERE]
  -- Look at your context!
  -- next_st has been beautifully computed as: ⟨n✝, i✝ ::ₘ w✝, c✝, q✝ ++ [i✝]⟩
  -- st has been locked in as: ⟨i✝ ::ₘ n✝, w✝, c✝, q✝⟩

  -- 2. Now we unfold the initial pattern to constrain those wild variables
  unfold init at h_init
  rcases h_init with ⟨i, S, h_eq, h_nodup⟩

  -- h_eq is now: ⟨i✝ ::ₘ n✝, w✝, c✝, q✝⟩ = ⟨i ::ₘ S, ∅, ∅, []⟩
  -- 3. We use `injection` to break this structure equality into 4 separate equations!
  injection h_eq with h_n h_w h_c h_q

  -- 4. Substitute the easy ones (Lists and empty sets aren't ambiguous)
  subst h_w h_c h_q

  -- [CLICK HERE]
  -- Look at `next_st` in your context now!
  -- It evaluates exactly to: ⟨n✝, i✝ ::ₘ ∅, ∅, [i✝]⟩

  -- And you are left with the mathematically correct constraint:
  -- h_n : i✝ ::ₘ n✝ = i ::ₘ S

  trivial


-- We use `example` for scratchpad testing.
-- We assume we have a starting state, a next state, and the rules applied to them.
example (st next_st : Conf) (h_init : init st) (h_step : step_n2w st next_st) : True := by

  -- 1. Unfold our initial pattern explicitly
  unfold init at h_init

  -- 2. Extract the variables (i, S) and substitute the exact state shape
  rcases h_init with ⟨i, S, rfl, h_nodup⟩

  -- [CLICK HERE IN YOUR EDITOR]
  -- Notice `h_step` in your Infoview.
  -- Lean's context now knows exactly what the starting state looks like:
  -- h_step : step_n2w ⟨i ::ₘ S, ∅, ∅, []⟩ next_st

  -- 3. THE MAGIC BULLET: Shatter the inductive transition!
  cases h_step

  -- [CLICK HERE IN YOUR EDITOR]
  -- Look at your Infoview now! Lean's unification engine just executed the rule.
  -- It has completely replaced `next_st` everywhere in the context with:
  -- ⟨S, {i}, ∅, [i]⟩

  -- We just end the dummy proof since we got what we wanted.
  trivial
