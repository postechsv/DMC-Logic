--- formalizing [1] https://www.gergeibana.com/NSLproofBC.pdf

import Mathlib.Data.List.Perm.Basic

inductive Msg where
  | err   : Msg -- alternative: using option monads
  | name  : String -> Msg
  | nonce : String -> Msg
  | enc   : Msg -> Msg -> Msg -> Msg
  | dec   : Msg -> Msg -> Msg -- destructor term
  | pk    : String -> Msg
  | sk    : String -> Msg
  | pair  : Msg -> Msg -> Msg
  | pi1   : Msg -> Msg -- destructor term
  | pi2   : Msg -> Msg -- destructor term
  deriving DecidableEq

abbrev MsgList := List Msg

def pi1 : Msg -> Msg
  | Msg.pair m _ => m
  | _ => Msg.err

def pi2 : Msg -> Msg
  | Msg.pair _ m => m
  | _ => Msg.err

-- alternative for pi1 and pi2
def eval : Msg -> Msg
  | Msg.pi1 (Msg.pair m _) => m
  | Msg.pi2 (Msg.pair _ m) => m
  | Msg.dec (Msg.enc m _ (Msg.pk str)) (Msg.sk str') =>
      if str = str' then m else Msg.err
  | m => m

inductive Subterm : Msg → Msg → Prop where
  | refl (m : Msg) : Subterm m m
  | pair1 {m m1 m2 : Msg} (h : Subterm m m1) : Subterm m (Msg.pair m1 m2)
  | pair2 {m m1 m2 : Msg} (h : Subterm m m2) : Subterm m (Msg.pair m1 m2)
  | enc1 {m m1 m2 m3 : Msg} (h : Subterm m m1) : Subterm m (Msg.enc m1 m2 m3)
  | enc2 {m m1 m2 m3 : Msg} (h : Subterm m m2) : Subterm m (Msg.enc m1 m2 m3)
  | enc3 {m m1 m2 m3 : Msg} (h : Subterm m m3) : Subterm m (Msg.enc m1 m2 m3)

/-
Discussion: should I include destructor terms in the definition of subterms?
-/

notation m1 " ⊑ " m2 => Subterm m1 m2

def Rand (m : Msg) : Prop :=
  match m with
  | Msg.nonce _ => true
  | _ => false

def Fresh (m : Msg) (ml : List Msg) : Prop := Rand m ∧ ∀ m' ∈ ml, ¬ Subterm m m'

opaque Derivable : MsgList → Msg → Prop
axiom der_refl : ∀ {ml m}, m ∈ ml → Derivable ml m
axiom der_weak : ∀ {ml m m'}, Derivable ml m → Derivable (m' :: ml) m
axiom der_comm : ∀ {ml ml' m}, ml.Perm ml' → Derivable ml' m → Derivable ml m
axiom der_trans : ∀ {ml m m'}, Derivable ml m' → Derivable (m' :: ml) m → Derivable ml m
axiom der_cong_pair : ∀ {ml m1 m2}, Derivable (m2::m1::ml) (Msg.pair m1 m2)
axiom der_cong_pi1 : ∀ {ml m}, Derivable ml m → Derivable ml (pi1 m)
axiom der_secrecy : ∀ {ml m m' r str}, ∀ m'' ∈ m'::ml, ¬ Subterm (Msg.sk str) m''
                    → Derivable (Msg.enc m' r (Msg.pk str)::ml) m → Derivable ml m
axiom no_telepathy : ∀ {ml m}, Fresh m ml → ¬ Derivable ml m

notation ml " |> " m => Derivable ml m

--- NSL
open Msg
def m1 := name "a"
def m2 := name "b"
def m3 := pk "a"
def m4 := pk "b"
def m5 := enc (pair (name "a") (nonce "n1")) (nonce "r1") (pk "b")

--- example 3.1 in [1]
example : [m1, m2, m3, m4, m5] |> m1 := by
  apply der_refl
  simp [m1]

--- example 3.2 in [1]
--- equation numberings in [1] match the hypotheses naming e.g., (1) <-> h1
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
    have h8' : ∀ m ∈ [m5, m4, m3, m2, m1], ¬ Subterm (Msg.sk "b") m := by
      intro m h h'


    simp [m5] at h7
    have h8' : ∀ m ∈ [pair (name "a") (nonce "n1"), m4, m3, m2, m1], ¬ Subterm (Msg.sk "b") m := by
      intro m h h'
      rcases h with hm5 | hm4 | hm3 | hm2 | hm1

      cases h
      nomatch h'
      cases a
      sorry

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
