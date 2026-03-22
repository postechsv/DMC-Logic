import Mathlib.Data.List.Perm.Basic

-- Msg (Subsorting)
inductive Msg where
  | err   : Msg
  | name  : String -> Msg
  | nonce : String -> Msg
  | enc   : Msg -> Msg -> Msg -> Msg
  | pair  : Msg -> Msg -> Msg
  | pk    : String -> Msg
  | sk    : String -> Msg
  deriving DecidableEq

def pi1 : Msg -> Msg
  | Msg.pair m _ => m
  | _ => Msg.err

def pi2 : Msg -> Msg
  | Msg.pair _ m => m
  | _ => Msg.err

inductive Subterm : Msg → Msg → Prop where
  | refl (m : Msg) : Subterm m m
  | pair1 {m m1 m2 : Msg} (h : Subterm m m1) : Subterm m (Msg.pair m1 m2)
  | pair2 {m m1 m2 : Msg} (h : Subterm m m2) : Subterm m (Msg.pair m1 m2)
  | enc1 {m m1 m2 m3 : Msg} (h : Subterm m m1) : Subterm m (Msg.enc m1 m2 m3)
  | enc2 {m m1 m2 m3 : Msg} (h : Subterm m m2) : Subterm m (Msg.enc m1 m2 m3)
  | enc3 {m m1 m2 m3 : Msg} (h : Subterm m m3) : Subterm m (Msg.enc m1 m2 m3)

def Rand (m : Msg) : Prop :=
  match m with
  | Msg.nonce _ => true
  | _ => false

def Fresh (m : Msg) (ml : List Msg) : Prop := ∀ m' ∈ ml, ¬ Subterm m m'

-- 2. Optional: Add a nice notation for it (e.g., ⊑)
notation m1 " ⊑ " m2 => Subterm m1 m2

-- MsgList
abbrev MsgList := List Msg

/-
-- State
inductive State where
  | mk (ml : MsgList) (cs : CState) : State

-- We can define your exact notation for State
notation "[" ml "|" cs "]" => State.mk ml cs
-/

--
-- inductive Derivable : MsgList → Msg → Prop where
--   | der_refl {ml m} (h_in : m ∈ ml) : Derivable ml m
--   | der_weak {ml m m'} (h : Derivable ml m) : Derivable (m' :: ml) m
--   | der_comm {ml ml' m} (h_perm : ml.Perm ml') (h : Derivable ml' m) : Derivable ml m
--   | der_trans {ml m m'} (h1 : Derivable ml m') (h2 : Derivable (m' :: ml) m) : Derivable ml m

axiom Derivable : MsgList → Msg → Prop
axiom der_refl : ∀ {ml m}, m ∈ ml → Derivable ml m
axiom der_weak : ∀ {ml m m'}, Derivable ml m → Derivable (m' :: ml) m
axiom der_comm : ∀ {ml ml' m}, ml.Perm ml' → Derivable ml' m → Derivable ml m
axiom der_trans : ∀ {ml m m'}, Derivable ml m' → Derivable (m' :: ml) m → Derivable ml m
axiom der_cong_pair : ∀ {ml m1 m2}, Derivable (m2::m1::ml) (Msg.pair m1 m2)
axiom der_cong_pi1 : ∀ {ml m}, Derivable ml m → Derivable ml (pi1 m)
---axiom cong_enc : ∀ {ml m1 m2 m3}, Derivable ml m1 → Derivable ml m2 → Derivable ml m3 → Derivable ml (enc m1 m2 m3)
axiom der_secrecy : ∀ {ml m m' r k}, Derivable (Msg.enc m' r k::ml) m -> Derivable ml m --- FIXME
axiom no_telepathy : ∀ {ml m}, Fresh m ml  → ¬ Derivable ml m
notation ml " |> " m => Derivable ml m


--- NSL

open Msg
def m1 := name "a"
def m2 := name "b"
def m3 := pk "a"
def m4 := pk "b"
def m5 := enc (pair (name "a") (nonce "n1")) (nonce "r1") (pk "b")

example : [m1, m2, m3, m4, m5] |> m1 := by
  apply der_refl
  simp [m1]

example : ¬ [m5, m4, m3, m2, m1] |> nonce "n1" := by
  intro h1
  have h2 : [m5, m4, m3, m2, m1] |> m1 := by
    have h2' : [m4, m3, m2, m1] |> m1 := by
      apply der_refl; simp [m1]
    apply der_weak; apply h2'
  have h4 : [m1, (nonce "n1"), m4, m3, m2, m1] |> pair (nonce "n1") m1 := by
    apply der_cong_pair
  have h5 : [m5, m1, (nonce "n1"), m4, m3, m2, m1] |> pair (nonce "n1") m1 := by
    apply der_weak; apply h4
  have h6 : [m1, (nonce "n1"), m5, m4, m3, m2, m1] |> pair (nonce "n1") m1 := by
    apply der_comm (ml' := m5 :: m1 :: (nonce "n1") :: m4 :: m3 :: m2 :: m1 :: [])
    rw [← List.isPerm_iff]
    decide
    apply h5
  have h7 : [m5, m4, m3, m2, m1] |> pair (nonce "n1") m1 := by
    sorry ---apply der_trans
  have h8 : [m4, m3, m2, m1] |> pair (nonce "n1") m1 := by
    apply der_secrecy h7 --- FIXME
  have h9 : [pair (nonce "n1") m1, m4, m3, m2, m1] |> pi1 (pair (nonce "n1") m1) := by
    apply der_cong_pi1
    apply der_refl; simp
  have h10 : [pair (nonce "n1") m1, m4, m3, m2, m1] |> (nonce "n1") := by
    dsimp [pi1] at h9; apply h9
  have h11 : [m4, m3, m2, m1] |> (nonce "n1") := by
    apply der_trans h8 h10
  have h12 : Fresh (nonce "n1") [m4, m3, m2, m1] := by
    simp [Fresh, m1, m2, m3, m4]
    constructor; intro h; cases h
    constructor; intro h; cases h
    constructor; intro h; cases h
    intro h; cases h
  apply no_telepathy h12; apply h11
