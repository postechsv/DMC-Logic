import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub


inductive Msg where
  | err : Msg -- alternative: using option monads
  --- constants
  | iA : Msg
  | iB : Msg
  | nA : Nat -> Msg --- parameterized by session id
  | nB : Nat -> Msg
  | r1 : Nat -> Msg
  | r2 : Nat -> Msg
  | r3 : Nat -> Msg
  | ok : Nat -> Msg
  --- assymetric encryption scheme
  | enc  : Msg -> Msg -> Msg -> Msg
  | dec  : Msg -> Msg -> Msg -- destructor term
  | pk   : Msg -> Msg
  | sk   : Msg -> Msg
  --- pairing
  | pair : Msg -> Msg -> Msg
  | fst  : Msg -> Msg -- destructor term
  | snd  : Msg -> Msg -- destructor term
  deriving DecidableEq

open Msg

def derivable (ml : List Msg) (m : Msg) : Prop := ∃ att : List Msg → Msg, att ml = m
notation ml "|>" m => derivable ml m


---abbrev MsgList := List Msg

--- Initiator Role
inductive ACtrl
  | a0 : ACtrl
  | a1 : ACtrl
  | a2 : ACtrl
  deriving DecidableEq

--- Responder Role
inductive BCtrl
  | b0 : BCtrl
  | b1 : BCtrl
  | b2 : BCtrl
  deriving DecidableEq

inductive Session
  | session (id : Nat) (a : ACtrl) (b : BCtrl)
  deriving DecidableEq
open Session

notation "$[" m "]" => Session.session m


--- global state with guard conditions
structure Conf where
  chan : List Msg
  ctrl : Multiset Session --- local states (e.g., active sessions)
  cond : Prop --- guard

--- transition relation
inductive Step : Conf → Conf → Prop where
  | a1 (i : Nat) (x : Msg) : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step { chan := ml, ctrl := {session i ACtrl.a0 cB} + ss, cond := p }
           { chan := (enc (pair (nA i) iA) (r1 i) (pk iB)) :: ml,
             ctrl := {session i ACtrl.a1 cB} + ss,
             cond := p ∧ (ml |> x) }
  | a2 (i : Nat) (x : Msg) : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step { chan := ml, ctrl := {session i ACtrl.a1 cB} + ss, cond := p }
           { chan := (enc (fst (snd (dec x (sk iA)))) (r3 i) (pk iB)) :: ml,
             ctrl := {session i ACtrl.a1 cB} + ss,
             cond := p ∧ (ml |> x) ∧ fst (dec x (sk iA)) = nA i ∧ snd (snd (dec x (sk iA))) = iB }
  | b1 (i : Nat) (x : Msg) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step { chan := ml, ctrl := {session i cA BCtrl.b0} + ss, cond := p }
           { chan := (enc (pair (fst (dec x (sk iB))) (pair (nB i) iB))
                          (r2 i) (pk (snd (dec x (sk iB))))) :: ml,
             ctrl := {session i cA BCtrl.b1} + ss,
             cond := p ∧ (ml |> x) }
  | b2 (i : Nat) (x : Msg) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step { chan := ml, ctrl := {session i cA BCtrl.b1} + ss, cond := p }
           { chan := ok i :: ml,
             ctrl := {session i cA BCtrl.b2} + ss,
             cond := p ∧ (ml |> x) ∧ dec x (sk iB) = nB i }

infix:110 " ⇒ " => Step
infix:110 " ⇒* " => Relation.ReflTransGen Step

def init1 : Conf := { chan := [], ctrl := {session 0 ACtrl.a0 BCtrl.b0}, cond := True }

example : init1 ⇒* init1 := by
  apply Relation.ReflTransGen.refl
