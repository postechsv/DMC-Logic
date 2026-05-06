import Bakery.S4

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.Group.Basic

---
--- defining NSL
---

--- syntax of NSL
inductive Msg where
  | err : Msg
  | none : Msg -- alternative: using option monads
  --- constants
  | iA : Msg
  | iB : Msg
  | iQ : Msg --- for guessing attack
  | nA : Nat -> Msg --- parameterized by session id
  | nB : Nat -> Msg
  | nQ : Msg --- for guessing attack
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

-- Destructors
---@[simp]
def fst : Msg → Msg
  | pair m1 _ => m1
  | _ => err

---@[simp]
def snd : Msg → Msg
  | pair _ m2 => m2
  | _ => err

---@[simp]
def dec : Msg → Msg → Msg
  | enc m _ (pk id1), sk id2 =>
      if id1 = id2 then m else err
  | _, _ => err

-- Remove @[simp] from the definitions of fst, snd, and dec!
-- Use these targeted reduction rules instead:
@[simp] lemma fst_pair_reduce (m1 m2 : Msg) : fst (pair m1 m2) = m1 := rfl
@[simp] lemma snd_pair_reduce (m1 m2 : Msg) : snd (pair m1 m2) = m2 := rfl
@[simp] lemma dec_enc_reduce (m r k : Msg) : dec (enc m r (pk k)) (sk k) = m := by
  unfold dec
  simp

---
--- Computational Equivalence Relation
---
class CompEquiv (K : KripkeFrame) where
  equiv : Msg → Msg → MProp K

  -- the following generates Prop
  refl  : ∀ w m , equiv m m w
  symm  : ∀ w m1 m2, equiv m1 m2 w → equiv m2 m1 w
  trans : ∀ w m1 m2 m3, equiv m1 m2 w → equiv m2 m3 w → equiv m1 m3 w



notation:50 m1 " ≈ " m2 => CompEquiv.equiv m1 m2

variable {K : KripkeFrame}
variable [CompEquiv K]

--- This is the magic line. It tells `simp` that anytime it sees `X ≈ X`,
--- it can instantly reduce it to `True`, mimicking strict equality.
-- @[simp]
-- lemma CompEquiv_refl {m : Msg} : m ≈ m := CompEquiv.refl m






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

---variable (comder : List Msg → Msg → MProp F)
axiom comder {K : KripkeFrame} : List Msg → Msg → MProp K
-- Notation for the modal derivability
notation ml " |> " m => comder ml m --- comder raises error!


--- global state
structure Conf (K : KripkeFrame) where
  chan : List Msg
  ctrl : Multiset Session --- caveat: can only have finite number of sessions
  cond : MProp K --- guard condition

--- transition relation
inductive Step {K : KripkeFrame} [CompEquiv K] (x : Msg) : Conf K → Conf K → Prop where
  | a1 (i : Nat)  : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : MProp K,
      Step x
        { chan := ml, ctrl := {session i ACtrl.a0 cB} + ss, cond := p }
        { chan := (enc (pair (nA i) iA) (r1 i) (pk iB)) :: ml,
          ctrl := {session i ACtrl.a1 cB} + ss,
          cond := □⋄(ml |> x) ⋏ p }
  | a2 (i : Nat) : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : MProp K,
      Step x
        { chan := ml, ctrl := {session i ACtrl.a1 cB} + ss, cond := p }
        { chan := (enc (fst (snd (dec x (sk iA)))) (r3 i) (pk iB)) :: ml,
          ctrl := {session i ACtrl.a2 cB} + ss,
          cond := □⋄(ml |> x) ⋏ □⋄(fst (dec x (sk iA)) ≈ nA i) ⋏ □⋄(snd (snd (dec x (sk iA))) ≈ iB) ⋏ p }
  | b1 (i : Nat) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session, ∀ p : MProp K,
      Step x
        { chan := ml, ctrl := {session i cA BCtrl.b0} + ss, cond := p }
        { chan := (enc (pair (fst (dec x (sk iB))) (pair (nB i) iB))
                      (r2 i) (pk (snd (dec x (sk iB))))) :: ml,
          ctrl := {session i cA BCtrl.b1} + ss,
          cond := □⋄(ml |> x) ⋏ p }
  | b2 (i : Nat) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session, ∀ p : MProp K,
      Step x
        { chan := ml, ctrl := {session i cA BCtrl.b1} + ss, cond := p }
        { chan := ok i :: ml,
          ctrl := {session i cA BCtrl.b2} + ss,
          cond := □⋄(ml |> x) ⋏ □⋄(dec x (sk iB) ≈ nB i) ⋏ p }

notation:110 st1 " ~(" x ")~> " st2 => Step x st1 st2

-- Labeled Reflexive-Transitive Closure
inductive Trace {K : KripkeFrame} [CompEquiv K] : List Msg → Conf K → Conf K → Prop where
  | refl (st : Conf K) : Trace [] st st
  | step {st1 st2 : Conf K} {x : Msg} :
      Step x st1 st2 →
      Trace [x] st1 st2
  | trans {st1 st2 st3 : Conf K} {xl1 xl2 : List Msg} :
      Trace xl1 st1 st2 →
      Trace xl2 st2 st3 →
      Trace (xl1 ++ xl2) st1 st3

-- Notation: Multi-step transition from st1 to st2, labeled with sequence xl
notation:110 st1 " ~(" xl ")~>* " st2 => Trace xl st1 st2

---
--- constructing the symbolic attack
---

def conf0 : Conf K := {
  chan := [],
  ctrl := {session 0 ACtrl.a0 BCtrl.b0, session 1 ACtrl.a0 BCtrl.b0},
  cond := mtrue
}

example : (conf0 : Conf K) ~([])~>* conf0 := by
  apply Trace.refl

--- output of a1
def m1 : Msg := enc (pair (nA 0) iA) (r1 0) (pk iB)

def conf1 : Conf K :=
  { chan := [m1],
    ctrl := {session 0 ACtrl.a1 BCtrl.b0, session 1 ACtrl.a0 BCtrl.b0},
    cond := □⋄([] |> none) ⋏ mtrue }

lemma step1 : (conf0 : Conf K) ~(Msg.none)~> conf1 := by
  apply Step.a1 0 [] BCtrl.b0 {session 1 ACtrl.a0 BCtrl.b0} mtrue

--- output of b1
def m2 : Msg := (enc (pair (fst (dec m1 (sk iB))) (pair (nB 0) iB))
                     (r2 0) (pk (snd (dec m1 (sk iB)))))

def conf2 : Conf K :=
  { chan := [m2, m1],
    ctrl := {session 0 ACtrl.a1 BCtrl.b1, session 1 ACtrl.a0 BCtrl.b0},
    cond := □⋄([m1] |> m1) ⋏ □⋄([] |> none) ⋏ mtrue }

lemma step2 : (conf1 : Conf K) ~(m1)~> conf2 := by
  apply Step.b1 0 [m1] ACtrl.a1 {session 1 ACtrl.a0 BCtrl.b0} (□⋄([] |> none) ⋏ mtrue)

--- output of a2
def m3 : Msg := (enc (fst (snd (dec m2 (sk iA)))) (r3 0) (pk iB))

def conf3 : Conf K :=
  { chan := [m3, m2, m1],
    ctrl := {session 0 ACtrl.a2 BCtrl.b1, session 1 ACtrl.a0 BCtrl.b0},
    cond := □⋄([m2, m1] |> m2)
            ⋏ □⋄(fst (dec m2 (sk iA)) ≈ nA 0) ⋏ □⋄(snd (snd (dec m2 (sk iA))) ≈ iB)
            ⋏ □⋄([m1] |> m1) ⋏ □⋄([] |> none) ⋏ mtrue }


lemma step3 : (conf2 : Conf K) ~(m2)~> conf3 := by
  apply Step.a2 0 [m2, m1] BCtrl.b1 {session 1 ACtrl.a0 BCtrl.b0} _

--- output of b1
def m4 : Msg := (enc (pair (fst (dec m3 (sk iB))) (pair (nB 1) iB))
                     (r2 1) (pk (snd (dec m3 (sk iB)))))

def conf4 : Conf K :=
  { chan := [m4, m3, m2, m1],
    ctrl := {session 0 ACtrl.a2 BCtrl.b1, session 1 ACtrl.a0 BCtrl.b1},
    cond := □⋄([m3, m2, m1] |> m3)
            ⋏ □⋄([m2, m1] |> m2)
            ⋏ □⋄(fst (dec m2 (sk iA)) ≈ nA 0) ⋏ □⋄(snd (snd (dec m2 (sk iA))) ≈ iB)
            ⋏ □⋄([m1] |> m1) ⋏ □⋄([] |> none) ⋏ mtrue }

--- TODO: difficulty in unification with + for multisets
lemma step4 : (conf3 : Conf K) ~(m3)~> conf4 := by
  sorry


lemma trace : ∃ ml, (conf0 : Conf K) ~(ml)~>* conf4 := by
  use [Msg.none, m1, m2, m3]
  exact Trace.trans (Trace.step step1) <|
        Trace.trans (Trace.step step2) <|
        Trace.trans (Trace.step step3) <|
                    (Trace.step step4)




---


--- computational assumption. should be justified "computationally"
--- i.e.: ∃ (w : K.World), ∀ (w' : K.World), K.R w w' ∧ (snd (nB 0) ≈ iQ) w'
---axiom weak_ambiguity : K.root ⊨ₛ₄ ⋄□(snd (nB 0) ≈ iQ)
axiom ambiguity : K.root ⊨ₛ₄ ⋄□(nB 0 ≈ pair nQ iQ)

--- computational secrecy
--- Mᶜ ⊨ₛ₄ ϕ
--- iff Mᶜ, Ω ⊨ₛ₄ ϕ   (... by def. in the paper)
--- iff Mᶜ, S ⊨ₛ₄ ϕ for any S ⊆ Ω   (... need to show this)

--- computational attack is the negation
--- Mᶜ, S ⊨ₛ₄ ϕ for some S ⊆ Ω

--- computational attack follows from symbolic attack
--- (need to show this by initiality of the symbolic model)
--- A, S ⊨ₛ₄ ϕ for some S ⊆ Ω

/-

-/



-- Notations (using standard modal logic unicode)
-- Type \rRightarrow for ⤇ and \Leftrightarrow for ⇔


axiom equiv_refl' : ∀ m, K.root ⊨ₛ₄ □⋄(m ≈ m)
axiom equiv_cong_der' : ∀ {ml m1 m2},
  K.root ⊨ₛ₄ □( □⋄(m1 ≈ m2) ⤇ □( □⋄(ml |> m1) ⇔ □⋄(ml |> m2) ) )

/--
Localized derivation congruence for indistinguishable messages.
Allows for immediate rewriting (rw) of deriving m1 to deriving m2.
-/
lemma equiv_cong_der {ml : List Msg} {m1 m2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_eq : □⋄(m1 ≈ m2) w) :
    □⋄(ml |> m1) w ↔ □⋄(ml |> m2) w := by
  have h_axiom := @equiv_cong_der' K _ (ml := ml) (m1 := m1) (m2 := m2)
  have h_impl := h_axiom w root_R_w
  have h_box_iff := h_impl h_eq
  have h_miff := h_box_iff w (K.refl w)
  exact h_miff

-- Axiom 1: Congruence of snd
axiom snd_cong' : ∀ {m1 m2},
  K.root ⊨ₛ₄ □( □⋄(m1 ≈ m2) ⤇ □⋄(snd m1 ≈ snd m2) )

lemma snd_cong {m1 m2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_eq : □⋄(m1 ≈ m2) w) : □⋄(snd m1 ≈ snd m2) w := by
  have h_axiom := @snd_cong' K _ (m1 := m1) (m2 := m2)
  have h_impl := h_axiom w root_R_w
  exact h_impl h_eq

-- Axiom 2: Congruence of pk
axiom pk_cong' : ∀ {m1 m2},
  K.root ⊨ₛ₄ □( □⋄(m1 ≈ m2) ⤇ □⋄(m1.pk ≈ m2.pk) )

lemma pk_cong {m1 m2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_eq : □⋄(m1 ≈ m2) w) : □⋄(m1.pk ≈ m2.pk) w := by
  have h_impl := pk_cong' (m1 := m1) (m2 := m2) w root_R_w
  exact h_impl h_eq

-- Axiom 3: Congruence of enc (on the key argument)
axiom enc_cong_key' : ∀ {m rand key1 key2},
  K.root ⊨ₛ₄ □( □⋄(key1 ≈ key2) ⤇ □⋄(enc m rand key1 ≈ enc m rand key2) )

lemma enc_cong_key {m rand key1 key2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_eq : □⋄(key1 ≈ key2) w) : □⋄(m.enc rand key1 ≈ m.enc rand key2) w := by
  have h_impl := enc_cong_key' (m := m) (rand := rand) (key1 := key1) (key2 := key2) w root_R_w
  exact h_impl h_eq

-- Full 3-ary parallel congruence for Encryption
axiom enc_cong' : ∀ {m1 m2 r1 r2 k1 k2},
  K.root ⊨ₛ₄ □( (□⋄(m1 ≈ m2) ⋏ □⋄(r1 ≈ r2) ⋏ □⋄(k1 ≈ k2)) ⤇ □⋄(enc m1 r1 k1 ≈ enc m2 r2 k2) )

/-- Localized full congruence for encryption -/
lemma enc_cong {m1 m2 r1 r2 k1 k2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w) (h_m : □⋄(m1 ≈ m2) w) (h_r : □⋄(r1 ≈ r2) w) (h_k : □⋄(k1 ≈ k2) w)
    : □⋄(enc m1 r1 k1 ≈ enc m2 r2 k2) w := by
  have h_impl := enc_cong' (m1 := m1) (m2 := m2) (r1 := r1) (r2 := r2) (k1 := k1) (k2 := k2) w root_R_w
  exact h_impl ⟨h_m, h_r, h_k⟩

axiom att_none' : ∀ {ml}, K.root ⊨ₛ₄ □⋄(ml |> none)
axiom att_mem' : ∀ {ml m}, m ∈ ml → (K.root ⊨ₛ₄ □⋄(ml |> m))

def leak :=
  ∃ st ml,
    (conf0 ~(ml)~>* st) ∧
    ∃ (w : K.World), w ⊨ₛ₄ (st.cond ⋏ □⋄(st.chan |> nB 0))




theorem attack : @leak K _ := by
  unfold leak
  obtain ⟨ml, h_trace⟩ := @trace K _
  obtain ⟨w, ⟨root_R_w, h_w⟩⟩ := @ambiguity K _
  use conf4; use ml; refine ⟨h_trace, ?_⟩
  use w -- the non-negligible world where ambiguity holds
  unfold conf4; simp [mand]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,?_⟩
  --- (click here to see all 8 proof obligations)
  · have h_mem : m3 ∈ [m3,m2,m1] := by simp
    apply persist_ow root_R_w (att_mem' h_mem)
  · have h_mem : m2 ∈ [m2,m1] := by simp
    apply persist_ow root_R_w (att_mem' h_mem)
  · simp [m1,m2] -- □⋄(nA 0 ≈ nA 0) w
    apply persist_ow root_R_w (equiv_refl' _)
  · simp [m1,m2] -- □⋄(iB ≈ iB) w
    apply persist_ow root_R_w (equiv_refl' _)
  · have h_mem : m1 ∈ [m1] := by simp
    apply persist_ow root_R_w (att_mem' h_mem)
  · apply persist_ow root_R_w att_none'
  · simp [mtrue]
  · --- (possible improvement: tactic for modal equational reasoning exploiting cut-elimination of s4)
    apply box_imp_box_dia at h_w

    rw [equiv_cong_der root_R_w h_w]

    have h_m4 : □⋄(m4 ≈ enc (pair (fst (pair nQ iQ)) (pair (nB 1) iB)) (r2 1) (pk iQ)) w := by
      apply snd_cong root_R_w at h_w
      apply pk_cong root_R_w at h_w
      apply enc_cong root_R_w



      apply enc_cong_key (m := pair (fst (nB 0)) (pair (nB 1) iB)) (rand := r2 1) root_R_w at h_w
      apply h_w






    have h_m4 : □⋄([m4, m3, m2, m1] |> m4) w := by
      apply persist_ow root_R_w
      apply att_mem'
      simp [m4, m3, m2, m1]
    simp [m1,m2,m3,m4] at h_m4

    ---intro w' w_R_w'
    ---have h_w' := h_w w' w_R_w'
    ---use w'; refine ⟨sorry, ?_⟩
    have h_cong_root := @equiv_cong_der' K _ (ml := [m4, m3, m2, m1]) (m1 := nB 0) (m2 := nQ.pair iQ)
    have h_cong_w := h_cong_root w root_R_w
    have h_w_dia : □⋄(nB 0 ≈ nQ.pair iQ) w := box_imp_box_dia h_w
    have h_iff_box := h_cong_w h_w_dia
    have h_iff := h_iff_box w (K.refl w)
    unfold miff at h_iff
    rw [h_iff]



    simp [m1,m2,m3,m4]



/-

-/






-- Assuming `mtrue` evaluates to `True` at world w
lemma persist_mtrue {K : KripkeFrame} {w w' : K.World}
    (h_R : K.R w w') (h_t : mtrue w) : mtrue w' := by
  exact h_t -- or `trivial`, depending on your exact definition

-- Assuming `(P ⋏ Q) w` evaluates to `P w ∧ Q w`
lemma persist_mand {K : KripkeFrame} {P Q : K.World → Prop} {w w' : K.World}
    (h_R : K.R w w')
    (hp : ∀ {v v'}, K.R v v' → P v → P v') -- P is persistent
    (hq : ∀ {v v'}, K.R v v' → Q v → Q v') -- Q is persistent
    (h_pq : (P ⋏ Q) w) : (P ⋏ Q) w' := by
  -- Unfold the modal conjunction
  rcases h_pq with ⟨h_P_w, h_Q_w⟩
  -- Apply persistence to both sides
  exact ⟨hp h_R h_P_w, hq h_R h_Q_w⟩
