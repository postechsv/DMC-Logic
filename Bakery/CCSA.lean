import Bakery.S4

/-
Built-in syntax for Protocol definition
-/

inductive Msg where
  | err : Msg
  | none : Msg
  --- constants
  | iA : Msg
  | iB : Msg
  | iQ : Msg
  | nA : Nat -> Msg
  | nB : Nat -> Msg
  | nQ : Msg
  | r1 : Nat -> Msg
  | r2 : Nat -> Msg
  | r3 : Nat -> Msg
  | ok : Nat -> Msg
  --- encryption
  | enc  : Msg -> Msg -> Msg -> Msg
  | pk   : Msg -> Msg
  | sk   : Msg -> Msg
  --- pairing
  | pair : Msg -> Msg -> Msg
  deriving DecidableEq
open Msg

def fst : Msg → Msg
  | pair m1 _ => m1
  | _ => err

def snd : Msg → Msg
  | pair _ m2 => m2
  | _ => err

def dec : Msg → Msg → Msg
  | enc m _ (pk id1), sk id2 =>
      if id1 = id2 then m else err
  | _, _ => err

@[simp] lemma fst_pair_reduce (m1 m2 : Msg) : fst (pair m1 m2) = m1 := rfl
@[simp] lemma snd_pair_reduce (m1 m2 : Msg) : snd (pair m1 m2) = m2 := rfl
@[simp] lemma dec_enc_reduce (m r k : Msg) : dec (enc m r (pk k)) (sk k) = m := by
  unfold dec
  simp

variable {K : KripkeFrame}



class CCSA (K : KripkeFrame) where
  equiv : Msg → Msg → MProp K -- equivalence
  deriv : List Msg → Msg → MProp K -- derivability
  indis : List Msg → Msg → MProp K -- indistinguishability

  /- structural axioms for equiv -/
  equiv_refl : ∀ m, K.root ⊨ₛ₄ □⋄(equiv m m)
  equiv_symm : ∀ {m1 m2}, K.root ⊨ₛ₄ □( □⋄(equiv m1 m2) ⤇ □⋄(equiv m2 m1) )
  equiv_trans : ∀ {m1 m2 m3}, K.root ⊨ₛ₄ □( (□⋄(equiv m1 m2) ⋏ □⋄(equiv m2 m3)) ⤇ □⋄(equiv m1 m3) )

  /- structural axioms for deriv -/
  deriv_none : ∀ {ml}, K.root ⊨ₛ₄ □⋄(deriv ml none)
  deriv_mem : ∀ {ml m}, m ∈ ml → (K.root ⊨ₛ₄ □⋄(deriv ml m))

  /- congruence axioms for equiv -/
  -- ...

  /- congruence axioms for deriv -/
  -- ...
  deriv_iQ : ∀ {ml}, K.root ⊨ₛ₄ □⋄(deriv ml iQ)
  deriv_sk : ∀ {ml m}, K.root ⊨ₛ₄ □( □⋄(deriv ml m) ⤇ □⋄(deriv ml (sk m)) )
  deriv_fst : ∀ {ml m}, K.root ⊨ₛ₄ □( □⋄(deriv ml m) ⤇ □⋄(deriv ml (fst m)) )
  deriv_pair : ∀ {ml m1 m2}, K.root ⊨ₛ₄ □( (□⋄(deriv ml m1) ⋏ □⋄(deriv ml m2)) ⤇ □⋄(deriv ml (pair m1 m2)) )
  deriv_dec : ∀ {ml m k}, K.root ⊨ₛ₄ □( (□⋄(deriv ml m) ⋏ □⋄(deriv ml k)) ⤇ □⋄(deriv ml (dec m k)) )


notation:50 ml " ▷ " m => CCSA.deriv ml m
notation:50 m1 " ≈ " m2 => CCSA.equiv m1 m2
