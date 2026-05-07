import Bakery.S4

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.Group.Basic

/-
LAYER 2: CCSA
-/

--- built-in syntax
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
-- the reason why we separtely define destructors is to exploit Lean's native simplification
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


-- TODO: move this into CCSA
axiom comder {K : KripkeFrame} : List Msg → Msg → MProp K
notation ml " |> " m => comder ml m --- comder raises error!

class CCSA (K : KripkeFrame) where
  equiv : Msg → Msg → MProp K

  -- the following generates Prop
  refl  : ∀ w m , equiv m m w
  symm  : ∀ w m1 m2, equiv m1 m2 w → equiv m2 m1 w
  trans : ∀ w m1 m2 m3, equiv m1 m2 w → equiv m2 m3 w → equiv m1 m3 w

  att_none' : ∀ {ml}, K.root ⊨ₛ₄ □⋄(ml |> none)
  att_mem' : ∀ {ml m}, m ∈ ml → (K.root ⊨ₛ₄ □⋄(ml |> m))


notation:50 m1 " ≈ " m2 => CCSA.equiv m1 m2

variable {K : KripkeFrame} -- we assume K faithfully represents possible worlds for PPTMs
variable [CCSA K] -- we assume CCSA axioms are consistent

-- @[simp]
-- lemma CCSA_refl {m : Msg} : m ≈ m := CCSA.refl m


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

--axiom att_none' : ∀ {ml}, K.root ⊨ₛ₄ □⋄(ml |> none)
--axiom att_mem' : ∀ {ml m}, m ∈ ml → (K.root ⊨ₛ₄ □⋄(ml |> m))

-- Congruence for fst (1 argument)
axiom fst_cong' : ∀ {m1 m2},
  K.root ⊨ₛ₄ □( □⋄(m1 ≈ m2) ⤇ □⋄(fst m1 ≈ fst m2) )

-- Congruence for sk (1 argument)
axiom sk_cong' : ∀ {m1 m2},
  K.root ⊨ₛ₄ □( □⋄(m1 ≈ m2) ⤇ □⋄(sk m1 ≈ sk m2) )

-- Full parallel congruence for pair (2 arguments)
axiom pair_cong' : ∀ {m1 m2 m3 m4},
  K.root ⊨ₛ₄ □( (□⋄(m1 ≈ m2) ⋏ □⋄(m3 ≈ m4)) ⤇ □⋄(pair m1 m3 ≈ pair m2 m4) )

-- Full parallel congruence for dec (2 arguments: ciphertext and key)
axiom dec_cong' : ∀ {c1 c2 k1 k2},
  K.root ⊨ₛ₄ □( (□⋄(c1 ≈ c2) ⋏ □⋄(k1 ≈ k2)) ⤇ □⋄(dec c1 k1 ≈ dec c2 k2) )

/-- Localized congruence for fst -/
lemma fst_cong {m1 m2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_eq : □⋄(m1 ≈ m2) w) : □⋄(fst m1 ≈ fst m2) w := by
  have h_impl := fst_cong' (m1 := m1) (m2 := m2) w root_R_w
  exact h_impl h_eq

/-- Localized congruence for sk -/
lemma sk_cong {m1 m2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_eq : □⋄(m1 ≈ m2) w) : □⋄(sk m1 ≈ sk m2) w := by
  have h_impl := sk_cong' (m1 := m1) (m2 := m2) w root_R_w
  exact h_impl h_eq

/-- Localized full parallel congruence for pair -/
lemma pair_cong {m1 m2 m3 m4 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_left : □⋄(m1 ≈ m2) w)
    (h_right : □⋄(m3 ≈ m4) w) : □⋄(pair m1 m3 ≈ pair m2 m4) w := by
  have h_impl := pair_cong' (m1 := m1) (m2 := m2) (m3 := m3) (m4 := m4) w root_R_w
  exact h_impl ⟨h_left, h_right⟩

/-- Localized full parallel congruence for decryption -/
lemma dec_cong {c1 c2 k1 k2 : Msg} {w : K.World}
    (root_R_w : K.R K.root w)
    (h_c : □⋄(c1 ≈ c2) w)
    (h_k : □⋄(k1 ≈ k2) w) : □⋄(dec c1 k1 ≈ dec c2 k2) w := by
  have h_impl := dec_cong' (c1 := c1) (c2 := c2) (k1 := k1) (k2 := k2) w root_R_w
  exact h_impl ⟨h_c, h_k⟩


/-
LAYER 3: NSL protocol
-/


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
structure Conf (K : KripkeFrame) where
  chan : List Msg
  ctrl : Multiset Session --- caveat: can only have finite number of sessions
  cond : MProp K --- guard condition

--- transition relation
inductive Step {K : KripkeFrame} [CCSA K] (x : Msg) : Conf K → Conf K → Prop where
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

inductive Trace {K : KripkeFrame} [CCSA K] : List Msg → Conf K → Conf K → Prop where
  | refl (st : Conf K) : Trace [] st st
  | step {st1 st2 : Conf K} {x : Msg} :
      Step x st1 st2 →
      Trace [x] st1 st2
  | trans {st1 st2 st3 : Conf K} {xl1 xl2 : List Msg} :
      Trace xl1 st1 st2 →
      Trace xl2 st2 st3 →
      Trace (xl1 ++ xl2) st1 st3

notation:110 st1 " ~(" x ")~> " st2 => Step x st1 st2
notation:110 st1 " ~(" xl ")~>* " st2 => Trace xl st1 st2


/-
LAYER 4: leak proof
-/


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


lemma trace : ∃ xl, (conf0 : Conf K) ~(xl)~>* conf4 := by
  use [Msg.none, m1, m2, m3]
  exact Trace.trans (Trace.step step1) <|
        Trace.trans (Trace.step step2) <|
        Trace.trans (Trace.step step3) <|
                    (Trace.step step4)


--- axiom weak_ambiguity : K.root ⊨ₛ₄ ⋄□(snd (nB 0) ≈ iQ)
axiom ambiguity : K.root ⊨ₛ₄ ⋄□(nB 0 ≈ pair nQ iQ)
/- computational assumption. should be justified "computationally"
   (proof sketch)
     construct a non-negligible set w of random tapes s.t.
     ∀ ρ ∈ w, ρ(nB 0) ≈ pair ρ(nQ) iQ
-/

--- computational secrecy
--- Mᶜ ⊨ₛ₄ ϕ
--- iff Mᶜ, Ω ⊨ₛ₄ ϕ   (... by def. in the paper)
--- iff Mᶜ, S ⊨ₛ₄ ϕ for any S ⊆ Ω   (... need to show this)

--- computational attack is the negation
--- Mᶜ, S ⊨ₛ₄ ϕ for some S ⊆ Ω

--- computational attack follows from symbolic attack
--- (need to show this by initiality of the symbolic model)
--- leak <=> A, S ⊨ₛ₄ ϕ for some S ⊆ Ω

def leak :=
  ∃ st ml,
    (conf0 ~(ml)~>* st) ∧
    ∃ (w : K.World), w ⊨ₛ₄ (st.cond ⋏ □⋄(st.chan |> nB 0))


-- (meeting: discuss 3 CLICKME's)
theorem attack : @leak K _ := by
  unfold leak
  obtain ⟨ml, h_trace⟩ := @trace K _
  use conf4; use ml; refine ⟨h_trace, ?_⟩

  -- (CLICKME: the non-negligible world where ambiguity holds "absolutely")
  obtain ⟨w, ⟨root_R_w, h_w⟩⟩ := @ambiguity K _; use w

  unfold conf4; simp [mand]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,?_⟩

  --- (CLICKME: all 8 proof obligations)
  · have h_mem : m3 ∈ [m3,m2,m1] := by simp
    apply persist_ow root_R_w (CCSA.att_mem' h_mem) -- (CLICKME: using both S4 & CCSA)
  · have h_mem : m2 ∈ [m2,m1] := by simp
    apply persist_ow root_R_w (CCSA.att_mem' h_mem)
  · simp [m1,m2] -- □⋄(nA 0 ≈ nA 0) w
    apply persist_ow root_R_w (equiv_refl' _)
  · simp [m1,m2] -- □⋄(iB ≈ iB) w
    apply persist_ow root_R_w (equiv_refl' _)
  · have h_mem : m1 ∈ [m1] := by simp
    apply persist_ow root_R_w (CCSA.att_mem' h_mem)
  · apply persist_ow root_R_w CCSA.att_none'
  · simp [mtrue]
  · --- STILL PROVING..
    apply box_imp_box_dia at h_w

    -- (CLICKME: potential tactic - equational reasoning under overwheming equivalences)
    -- discussion: could this be further improved as tactics?
    rw [equiv_cong_der root_R_w h_w] -- see how nB 0 is rewritten via congruence axiom in CCSA

    have h_m4 : □⋄(m4 ≈ enc (pair (fst (pair nQ iQ)) (pair (nB 1) iB)) (r2 1) (pk iQ)) w := by
      apply snd_cong root_R_w at h_w
      simp at h_w
      apply pk_cong root_R_w at h_w
      apply enc_cong root_R_w
      · sorry
      · sorry
      · simp [m3, m2, m1, h_w]
    simp at h_m4 -- TODO: merge

    have h_m4' : □⋄( pair (fst (dec m4 (sk iQ))) iQ ≈ pair (fst (dec ((nQ.pair ((nB 1).pair iB)).enc (r2 1) iQ.pk) (sk iQ))) iQ ) w := by
      sorry
    simp at h_m4' -- TODO: merge

    have guess : □⋄([m4, m3, m2, m1] |> pair (fst (dec m4 (sk iQ))) iQ) w := by
      sorry

    sorry
