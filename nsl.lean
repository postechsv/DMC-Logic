import Bakery.CCSA

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

open Msg

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

--- global state
structure Conf where
  chan : List Msg
  ctrl : Multiset Session --- caveat: can only have finite number of sessions

--- transition relation
--- Note Step is parameterized by world w
--- Hence, trace would also be parameterized by a decreasing chain of worlds
inductive Step {K : KripkeFrame} [CCSA K] (w : K.World) (x : Msg) : Conf → Conf → Prop where
  | a1 (i : Nat)  : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session,
      □⋄(ml ▷ x) w
      → Step w x
        { chan := ml, ctrl := {session i ACtrl.a0 cB} + ss }
        { chan := (enc (pair (nA i) iA) (r1 i) (pk iB)) :: ml,
          ctrl := {session i ACtrl.a1 cB} + ss }
  | a2 (i : Nat) : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session,
      (□⋄(ml ▷ x) ⋏ □⋄(fst (dec x (sk iA)) ≈ nA i) ⋏ □⋄(snd (snd (dec x (sk iA))) ≈ iB)) w
      → Step w x
        { chan := ml, ctrl := {session i ACtrl.a1 cB} + ss }
        { chan := (enc (fst (snd (dec x (sk iA)))) (r3 i) (pk iB)) :: ml,
          ctrl := {session i ACtrl.a2 cB} + ss }
  | b1 (i : Nat) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session,
      (□⋄(ml ▷ x)) w
      → Step w x
        { chan := ml, ctrl := {session i cA BCtrl.b0} + ss }
        { chan := (enc (pair (fst (dec x (sk iB))) (pair (nB i) iB))
                      (r2 i) (pk (snd (dec x (sk iB))))) :: ml,
          ctrl := {session i cA BCtrl.b1} + ss }
  | b2 (i : Nat) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session,
      (□⋄(ml ▷ x) ⋏ □⋄(dec x (sk iB) ≈ nB i)) w
      → Step w x
        { chan := ml, ctrl := {session i cA BCtrl.b1} + ss }
        { chan := ok i :: ml,
          ctrl := {session i cA BCtrl.b2} + ss }


--- guarded Conf
structure GConf {K : KripkeFrame} where
  conf : Conf
  cond : Conf → MProp K

-- same signature as Step, except for GConf
def GStep {K : KripkeFrame} [CCSA K] (w : K.World) (x : Msg) (c1 : @GConf K) (c2 : @GConf K) : Prop :=
  (c1.cond c1.conf) w -> (@Step K _  w x c1.conf c2.conf)

--- world should be explicit in the notation
notation:110 st1 " ~(" w " , "x ")~> " st2 => GStep w x st1 st2


/- end of NSL definition -/


def conf0 : Conf := {
  chan := [],
  ctrl := {session 0 ACtrl.a0 BCtrl.b0, session 1 ACtrl.a0 BCtrl.b0},
}
def pred0 {K : KripkeFrame} [CCSA K] (_ : Conf) : MProp K := mtrue
def cf0 {K : KripkeFrame} [CCSA K] : @GConf K := { conf := conf0, cond := pred0 }

--- output of a1
def m1 : Msg := enc (pair (nA 0) iA) (r1 0) (pk iB)

def conf1 : Conf :=
  { chan := [m1],
    ctrl := {session 0 ACtrl.a1 BCtrl.b0, session 1 ACtrl.a0 BCtrl.b0} }
def pred1 {K : KripkeFrame} [CCSA K] (_ : Conf) : MProp K := fun w => (□⋄([] ▷ none) ⋏ mtrue)  w
def cf1 {K : KripkeFrame} [CCSA K] : @GConf K := { conf := conf1, cond := pred1 }

lemma step1 {K : KripkeFrame} [CCSA K] : cf0 ~( K.root , none )~> cf1 := by
  unfold GStep
  simp [cf0, pred0]
  intro h_cond
  apply Step.a1 0 [] BCtrl.b0 {session 1 ACtrl.a0 BCtrl.b0}
  /- sat check: K.root ⊨ₛ₄ □⋄([] ▷ Msg.none) -/
  apply CCSA.deriv_none







inductive Trace {K : KripkeFrame} [CCSA K] : List Msg → Conf K → Conf K → Prop where
  | refl (st : Conf K) : Trace [] st st
  | step {st1 st2 : Conf K} {x : Msg} :
      Step x st1 st2 →
      Trace [x] st1 st2
  | trans {st1 st2 st3 : Conf K} {xl1 xl2 : List Msg} :
      Trace xl1 st1 st2 →
      Trace xl2 st2 st3 →
      Trace (xl1 ++ xl2) st1 st3

notation:110 st1 " ~(" xl ")~>* " st2 => Trace xl st1 st2
