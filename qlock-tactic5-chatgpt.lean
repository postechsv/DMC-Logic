/-
Objective: generic ACU mgu certification tactic
-/

import Bakery.DMC3
import Bakery.command

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Multiset.Bind


import Mathlib.Tactic.IntervalCases

open Lean Meta Elab Tactic

open Multiset

namespace ACUCert

section Basic

variable {α : Type} [DecidableEq α]

/--
First tiny tactic.

It proves multiset equalities by extensionality:
two multisets are equal if every element has the same count.
Then `simp` reduces counts of sums to arithmetic.
-/
macro "acu_ext" : tactic =>
  `(tactic|
    (ext a <;>
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]))

/-
Basic sanity tests.
These are not unification completeness yet.
They only test that we can reason modulo ACU for multisets.
-/

example (X Y : Multiset α) :
    X + Y = Y + X := by
  acu_ext

example (X Y Z : Multiset α) :
    (X + Y) + Z = X + (Y + Z) := by
  acu_ext

example (X Y Z : Multiset α) :
    X + Y + Z = Z + X + Y := by
  acu_ext

example (X : Multiset α) :
    X + 0 = X := by
  acu_ext

example (X : Multiset α) :
    0 + X = X := by
  acu_ext

/--
Given an ACU equality, extract its pointwise count equation.

This is the first bridge from multisets to arithmetic.
-/
example (X Y A B : Multiset α) (h : X + Y = A + B) (e : α) :
    count e X + count e Y = count e A + count e B := by
  have h' := congrArg (count e) h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

end Basic


section ArithmeticKernels

/--
Pointwise certification kernel for:

  X + Y = A + B

For a fixed element e, write:

  x = count e X
  y = count e Y
  a = count e A
  b = count e B

Then the premise becomes:

  x + y = a + b

The certificate schema says that there are four pieces:

  u₁ : X-A part
  u₂ : Y-A part
  u₃ : X-B part
  u₄ : Y-B part
-/
lemma pointwise_ex2
    (x y a b : Nat)
    (h : x + y = a + b) :
    ∃ u₁ u₂ u₃ u₄ : Nat,
      x = u₁ + u₃ ∧
      y = u₂ + u₄ ∧
      a = u₁ + u₂ ∧
      b = u₃ + u₄ := by
  by_cases hxa : x ≤ a
  · -- Case 1: X is no larger than A.
    -- Put all of X into the X-A overlap.
    refine ⟨x, a - x, 0, b, ?_⟩
    omega
  · -- Case 2: X is larger than A.
    -- Put all of A into the X-A overlap.
    have hax : a ≤ x := Nat.le_of_not_ge hxa
    refine ⟨a, 0, x - a, y, ?_⟩
    omega




def ex2_u₁ (x a : Nat) : Nat :=
  if x ≤ a then x else a

def ex2_u₂ (x a : Nat) : Nat :=
  if x ≤ a then a - x else 0

def ex2_u₃ (x a : Nat) : Nat :=
  if x ≤ a then 0 else x - a

def ex2_u₄ (x y a b : Nat) : Nat :=
  if x ≤ a then b else y



lemma pointwise_ex2_explicit
    (x y a b : Nat)
    (h : x + y = a + b) :
    x = ex2_u₁ x a + ex2_u₃ x a ∧
    y = ex2_u₂ x a + ex2_u₄ x y a b ∧
    a = ex2_u₁ x a + ex2_u₂ x a ∧
    b = ex2_u₃ x a + ex2_u₄ x y a b := by
  unfold ex2_u₁ ex2_u₂ ex2_u₃ ex2_u₄
  by_cases hxa : x ≤ a
  · simp [hxa]
    omega
  · have hax : a ≤ x := Nat.le_of_not_ge hxa
    simp [hxa]
    omega

lemma pointwise_ex2'
    (x y a b : Nat)
    (h : x + y = a + b) :
    ∃ u₁ u₂ u₃ u₄ : Nat,
      x = u₁ + u₃ ∧
      y = u₂ + u₄ ∧
      a = u₁ + u₂ ∧
      b = u₃ + u₄ := by
  refine ⟨ex2_u₁ x a, ex2_u₂ x a, ex2_u₃ x a, ex2_u₄ x y a b, ?_⟩
  exact pointwise_ex2_explicit x y a b h


















/--
Pointwise certification kernel for:

  X + X = A + B

For a fixed element e:

  2 * x = a + b

The Hilbert basis has three atomic patterns:

  [1,2,0]
  [1,1,1]
  [1,0,2]

So the certificate shape is:

  x = u + v + w
  a = u + u + v
  b = v + w + w
-/
lemma pointwise_double
    (x a b : Nat)
    (h : x + x = a + b) :
    ∃ u v w : Nat,
      x = u + v + w ∧
      a = u + u + v ∧
      b = v + w + w := by
  --omega
  sorry

/--
Ground distribution kernel for:

  X + Y = {a}

For one distinguished element, if its total count is 1,
then it belongs either to X or to Y.
-/
lemma pointwise_one
    (x y : Nat)
    (h : x + y = 1) :
    (x = 1 ∧ y = 0) ∨
    (x = 0 ∧ y = 1) := by
  omega

/--
Ground distribution kernel for two copies of the same element:

  X + Y = {a} + {a}

For the distinguished element:

  x + y = 2

There are three possibilities.
-/
lemma pointwise_two_same
    (x y : Nat)
    (h : x + y = 2) :
    (x = 2 ∧ y = 0) ∨
    (x = 1 ∧ y = 1) ∨
    (x = 0 ∧ y = 2) := by
  omega

end ArithmeticKernels

section MkWitnessList

variable {α : Type} [DecidableEq α]

/--
`mkWitnessList xs f` builds a multiset containing `f a` copies of each
element `a` in the support list `xs`.

We will require `xs.Nodup` in the main count lemma.
-/
def mkWitnessList : List α → (α → Nat) → Multiset α
  | [], _ => 0
  | x :: xs, f => Multiset.replicate (f x) x + mkWitnessList xs f

/--
Main correctness lemma for `mkWitnessList`.

If `xs` has no duplicates, then the count of `e` in the constructed multiset is:

  f e, if e is in the support;
  0, otherwise.
-/
lemma count_mkWitnessList
    (xs : List α)
    (hxs : xs.Nodup)
    (f : α → Nat)
    (e : α) :
    Multiset.count e (mkWitnessList xs f) =
      if e ∈ xs then f e else 0 := by
  induction xs with
  | nil =>
      simp [mkWitnessList]
  | cons x xs ih =>
      simp [List.nodup_cons] at hxs
      rcases hxs with ⟨hx_not_mem, hxs_nodup⟩
      by_cases hex : e = x
      · subst e
        simp [
          mkWitnessList,
          ih hxs_nodup,
          hx_not_mem,
          Multiset.count_replicate
        ]
      · have hxe : x ≠ e := by
          intro h
          exact hex h.symm
        simp [
          mkWitnessList,
          ih hxs_nodup,
          hex,
          hxe,
          Multiset.count_replicate
        ]

/-
Small tests.
-/

example :
    Multiset.count 1
      (mkWitnessList ([1, 2] : List Nat)
        (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0))
      = 3 := by
  have hnd : ([1, 2] : List Nat).Nodup := by decide
  simpa using
    (count_mkWitnessList
      ([1, 2] : List Nat)
      hnd
      (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0)
      1)

example :
    Multiset.count 2
      (mkWitnessList ([1, 2] : List Nat)
        (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0))
      = 4 := by
  have hnd : ([1, 2] : List Nat).Nodup := by decide
  simpa using
    (count_mkWitnessList
      ([1, 2] : List Nat)
      hnd
      (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0)
      2)

example :
    Multiset.count 3
      (mkWitnessList ([1, 2] : List Nat)
        (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0))
      = 0 := by
  have hnd : ([1, 2] : List Nat).Nodup := by decide
  simpa using
    (count_mkWitnessList
      ([1, 2] : List Nat)
      hnd
      (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0)
      3)

end MkWitnessList


end ACUCert


namespace ACUCert

open Multiset

section CompletenessEx2WithSupport

variable {α : Type} [DecidableEq α]

/--
Finite-support version of the completeness theorem for

  X + Y = A + B.

The support list `xs` is assumed to contain every element that occurs in
`X`, `Y`, `A`, or `B`.

Later, the tactic will generate such an `xs` automatically from the input
multisets. For now, we keep it explicit so the proof is debuggable.
-/
lemma completeness_ex2_with_support
    (xs : List α)
    (hxs : xs.Nodup)
    (X Y A B : Multiset α)
    (hX : ∀ e, e ∉ xs → Multiset.count e X = 0)
    (hY : ∀ e, e ∉ xs → Multiset.count e Y = 0)
    (hA : ∀ e, e ∉ xs → Multiset.count e A = 0)
    (hB : ∀ e, e ∉ xs → Multiset.count e B = 0)
    (h : X + Y = A + B) :
    ∃ U₁ U₂ U₃ U₄ : Multiset α,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by

  let f₁ : α → Nat :=
    fun e => ex2_u₁ (Multiset.count e X) (Multiset.count e A)

  let f₂ : α → Nat :=
    fun e => ex2_u₂ (Multiset.count e X) (Multiset.count e A)

  let f₃ : α → Nat :=
    fun e => ex2_u₃ (Multiset.count e X) (Multiset.count e A)

  let f₄ : α → Nat :=
    fun e =>
      ex2_u₄
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)

  let U₁ : Multiset α := mkWitnessList xs f₁
  let U₂ : Multiset α := mkWitnessList xs f₂
  let U₃ : Multiset α := mkWitnessList xs f₃
  let U₄ : Multiset α := mkWitnessList xs f₄

  refine ⟨U₁, U₂, U₃, U₄, ?_, ?_, ?_, ?_⟩

  · -- X = U₁ + U₃
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases hem : e ∈ xs
    · simpa [
        U₁, U₃, f₁, f₃,
        count_mkWitnessList,
        hxs,
        hem,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.1
    · have hx0 : Multiset.count e X = 0 := hX e hem
      simp [
        U₁, U₃, f₁, f₃,
        count_mkWitnessList,
        hxs,
        hem,
        hx0
      ]

  · -- Y = U₂ + U₄
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases hem : e ∈ xs
    · simpa [
        U₂, U₄, f₂, f₄,
        count_mkWitnessList,
        hxs,
        hem,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.2.1
    · have hy0 : Multiset.count e Y = 0 := hY e hem
      simp [
        U₂, U₄, f₂, f₄,
        count_mkWitnessList,
        hxs,
        hem,
        hy0
      ]

  · -- A = U₁ + U₂
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases hem : e ∈ xs
    · simpa [
        U₁, U₂, f₁, f₂,
        count_mkWitnessList,
        hxs,
        hem,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.2.2.1
    · have ha0 : Multiset.count e A = 0 := hA e hem
      simp [
        U₁, U₂, f₁, f₂,
        count_mkWitnessList,
        hxs,
        hem,
        ha0
      ]

  · -- B = U₃ + U₄
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases hem : e ∈ xs
    · simpa [
        U₃, U₄, f₃, f₄,
        count_mkWitnessList,
        hxs,
        hem,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.2.2.2
    · have hb0 : Multiset.count e B = 0 := hB e hem
      simp [
        U₃, U₄, f₃, f₄,
        count_mkWitnessList,
        hxs,
        hem,
        hb0
      ]

end CompletenessEx2WithSupport

end ACUCert


section MkWitnessMultiset

variable {α : Type} [DecidableEq α]

/--
`mkWitness s f` builds a multiset containing `f a` copies of each element
`a` in the support multiset `s`.

We will use it with `s = (X + Y + A + B).dedup`.
-/
def mkWitness (s : Multiset α) (f : α → Nat) : Multiset α :=
  s.bind (fun a => Multiset.replicate (f a) a)

/--
Main count lemma for `mkWitness`.

If `s` is duplicate-free, then the count of `e` in `mkWitness s f` is:

  f e, if e ∈ s;
  0, otherwise.
-/
lemma count_mkWitness
    (s : Multiset α)
    (hs : s.Nodup)
    (f : α → Nat)
    (e : α) :
    Multiset.count e (mkWitness s f) =
      if e ∈ s then f e else 0 := by
  revert hs f e
  refine Multiset.induction_on s ?nil ?cons
  · intro hs f e
    simp [mkWitness]
  · intro x s ih hs f e
    simp at hs
    rcases hs with ⟨hx_not_mem, hs_nodup⟩
    by_cases hex : e = x
    · subst e
      simp [
        mkWitness,
        ih hs_nodup f x,
        hx_not_mem,
        Multiset.count_replicate
      ]
      · intro y hy
        have hxy : x ≠ y := by
          intro h
          exact hx_not_mem (h ▸ hy)
        simp [Multiset.mem_replicate, hxy, eq_comm]
    · have hxe : x ≠ e := by
        intro h
        exact hex h.symm
      simp [
        mkWitness,
        ih hs_nodup f e,
        hex,
        hxe,
        Multiset.count_replicate
      ]
      · simpa [mkWitness] using ih hs_nodup f e

example :
    Multiset.count 1
      (mkWitness ({1, 2} : Multiset Nat)
        (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0))
      = 3 := by
  have hnd : ({1, 2} : Multiset Nat).Nodup := by decide
  simpa using
    (count_mkWitness
      ({1, 2} : Multiset Nat)
      hnd
      (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0)
      1)

example :
    Multiset.count 2
      (mkWitness ({1, 2} : Multiset Nat)
        (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0))
      = 4 := by
  have hnd : ({1, 2} : Multiset Nat).Nodup := by decide
  simpa using
    (count_mkWitness
      ({1, 2} : Multiset Nat)
      hnd
      (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0)
      2)

example :
    Multiset.count 3
      (mkWitness ({1, 2} : Multiset Nat)
        (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0))
      = 0 := by
  have hnd : ({1, 2} : Multiset Nat).Nodup := by decide
  simpa using
    (count_mkWitness
      ({1, 2} : Multiset Nat)
      hnd
      (fun n : Nat => if n = 1 then 3 else if n = 2 then 4 else 0)
      3)

end MkWitnessMultiset



section CompletenessEx2AutoSupport

variable {α : Type} [DecidableEq α]

/--
If `e` is not in the deduplicated support of `X + Y + A + B`,
then its count is zero in each of `X`, `Y`, `A`, and `B`.
-/
lemma count_zero_of_notMem_sum4_dedup
    (X Y A B : Multiset α)
    {e : α}
    (heS : e ∉ (X + Y + A + B).dedup) :
    Multiset.count e X = 0 ∧
    Multiset.count e Y = 0 ∧
    Multiset.count e A = 0 ∧
    Multiset.count e B = 0 := by
  have heSum : e ∉ X + Y + A + B := by
    intro he
    exact heS (by simpa using he)

  have heX : e ∉ X := by
    intro hx
    exact heSum (by simp [hx])

  have heY : e ∉ Y := by
    intro hy
    exact heSum (by simp [hy])

  have heA : e ∉ A := by
    intro ha
    exact heSum (by simp [ha])

  have heB : e ∉ B := by
    intro hb
    exact heSum (by simp [hb])

  exact
    ⟨ Multiset.count_eq_zero_of_notMem heX
    , Multiset.count_eq_zero_of_notMem heY
    , Multiset.count_eq_zero_of_notMem heA
    , Multiset.count_eq_zero_of_notMem heB
    ⟩


def ex2_u₁ (x a : Nat) : Nat :=
  if x ≤ a then x else a

def ex2_u₂ (x a : Nat) : Nat :=
  if x ≤ a then a - x else 0

def ex2_u₃ (x a : Nat) : Nat :=
  if x ≤ a then 0 else x - a

def ex2_u₄ (x y a b : Nat) : Nat :=
  if x ≤ a then b else y

lemma pointwise_ex2_explicit
    (x y a b : Nat)
    (h : x + y = a + b) :
    x = ex2_u₁ x a + ex2_u₃ x a ∧
    y = ex2_u₂ x a + ex2_u₄ x y a b ∧
    a = ex2_u₁ x a + ex2_u₂ x a ∧
    b = ex2_u₃ x a + ex2_u₄ x y a b := by
  unfold ex2_u₁ ex2_u₂ ex2_u₃ ex2_u₄
  by_cases hxa : x ≤ a
  · simp [hxa]
    omega
  · have hax : a ≤ x := Nat.le_of_not_ge hxa
    simp [hxa]
    omega

/--
Automatic-support version of the completeness certificate for

  X + Y = A + B.

This is the first real target lemma.
-/
lemma completeness_ex2
    (X Y A B : Multiset α)
    (h : X + Y = A + B) :
    ∃ U₁ U₂ U₃ U₄ : Multiset α,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by

  let S : Multiset α := (X + Y + A + B).dedup

  have hS : S.Nodup := by
    simpa [S] using Multiset.nodup_dedup (X + Y + A + B)

  let f₁ : α → Nat :=
    fun e => ex2_u₁ (Multiset.count e X) (Multiset.count e A)

  let f₂ : α → Nat :=
    fun e => ex2_u₂ (Multiset.count e X) (Multiset.count e A)

  let f₃ : α → Nat :=
    fun e => ex2_u₃ (Multiset.count e X) (Multiset.count e A)

  let f₄ : α → Nat :=
    fun e =>
      ex2_u₄
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)

  let U₁ : Multiset α := mkWitness S f₁
  let U₂ : Multiset α := mkWitness S f₂
  let U₃ : Multiset α := mkWitness S f₃
  let U₄ : Multiset α := mkWitness S f₄

  refine ⟨U₁, U₂, U₃, U₄, ?_, ?_, ?_, ?_⟩

  · -- X = U₁ + U₃
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases heS : e ∈ S
    · simpa [
        U₁, U₃, f₁, f₃, S,
        count_mkWitness, hS, heS,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.1
    · have hz := count_zero_of_notMem_sum4_dedup X Y A B (by simpa [S] using heS)
      rcases hz with ⟨hx0, hy0, ha0, hb0⟩
      simp [
        U₁, U₃, f₁, f₃, S,
        count_mkWitness, hS, heS,
        hx0
      ]

  · -- Y = U₂ + U₄
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases heS : e ∈ S
    · simpa [
        U₂, U₄, f₂, f₄, S,
        count_mkWitness, hS, heS,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.2.1
    · have hz := count_zero_of_notMem_sum4_dedup X Y A B (by simpa [S] using heS)
      rcases hz with ⟨hx0, hy0, ha0, hb0⟩
      simp [
        U₂, U₄, f₂, f₄, S,
        count_mkWitness, hS, heS,
        hy0
      ]

  · -- A = U₁ + U₂
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases heS : e ∈ S
    · simpa [
        U₁, U₂, f₁, f₂, S,
        count_mkWitness, hS, heS,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.2.2.1
    · have hz := count_zero_of_notMem_sum4_dedup X Y A B (by simpa [S] using heS)
      rcases hz with ⟨hx0, hy0, ha0, hb0⟩
      simp [
        U₁, U₂, f₁, f₂, S,
        count_mkWitness, hS, heS,
        ha0
      ]

  · -- B = U₃ + U₄
    ext e
    have hcount :
        Multiset.count e X + Multiset.count e Y =
        Multiset.count e A + Multiset.count e B := by
      have hc := congrArg (fun M => Multiset.count e M) h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

    have hp :=
      pointwise_ex2_explicit
        (Multiset.count e X)
        (Multiset.count e Y)
        (Multiset.count e A)
        (Multiset.count e B)
        hcount

    by_cases heS : e ∈ S
    · simpa [
        U₃, U₄, f₃, f₄, S,
        count_mkWitness, hS, heS,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
      ] using hp.2.2.2
    · have hz := count_zero_of_notMem_sum4_dedup X Y A B (by simpa [S] using heS)
      rcases hz with ⟨hx0, hy0, ha0, hb0⟩
      simp [
        U₃, U₄, f₃, f₄, S,
        count_mkWitness, hS, heS,
        hb0
      ]


example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  intro h
  exact completeness_ex2 X Y A B h


end CompletenessEx2AutoSupport


namespace ACUCert

open Lean Elab Tactic

/--
First tiny tactic wrapper.

It solves goals of the shape:

  X + Y = A + B →
  ∃ U₁ U₂ U₃ U₄,
    X = U₁ + U₃ ∧
    Y = U₂ + U₄ ∧
    A = U₁ + U₂ ∧
    B = U₃ + U₄

by applying the certified theorem `completeness_ex2`.
-/
macro "acu_cert_ex2" : tactic =>
  `(tactic|
    first
      | exact ACUCert.completeness_ex2 _ _ _ _ ‹_›
      | intro h
        exact ACUCert.completeness_ex2 _ _ _ _ h)

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_ex2

example (X Y A B : Multiset Nat)
    (h : X + Y = A + B) :
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_ex2

end ACUCert
