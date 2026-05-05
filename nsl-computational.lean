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
  | nQ : Nat -> Msg --- for guessing attack
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

  --surj_pair : ∀ {m}, equiv (pair (fst m) (snd m)) m
  --pair_cong_snd : ∀ {m1 m2 m3}, equiv m2 m3 → equiv (pair m1 m2) (pair m1 m3)
  --enc_cong_pk   : ∀ {m r k1 k2}, equiv k1 k2 → equiv (enc m r (pk k1)) (enc m r (pk k2))

notation:50 m1 " ≈ " m2 => CompEquiv.equiv m1 m2

variable {K : KripkeFrame}
variable [CompEquiv K]

--- This is the magic line. It tells `simp` that anytime it sees `X ≈ X`,
--- it can instantly reduce it to `True`, mimicking strict equality.
-- @[simp]
-- lemma CompEquiv_refl {m : Msg} : m ≈ m := CompEquiv.refl m




---
--- attacker model (loose semantics)
---
class AttackerModel where
  derivable : List Msg → Msg → Prop

  -- Axioms refer directly to the internal `derivable` field
  att_none : ∀ {ml}, derivable ml Msg.none
  att_mem  : ∀ {ml m}, m ∈ ml → derivable ml m
  att_pair : ∀ {ml m1 m2}, derivable ml m1 → derivable ml m2 → derivable ml (pair m1 m2)
  att_fst  : ∀ {ml m1 m2}, derivable ml (pair m1 m2) → derivable ml m1
  att_snd  : ∀ {ml m1 m2}, derivable ml (pair m1 m2) → derivable ml m2
  att_enc  : ∀ {ml m r k}, derivable ml m → derivable ml r → derivable ml (pk k) → derivable ml (enc m r (pk k))
  att_dec  : ∀ {ml m r k}, derivable ml (enc m r (pk k)) → derivable ml (sk k) → derivable ml m

  -- NEW: Attacker knows their own identity and key
  att_iQ   : ∀ {ml}, derivable ml iQ
  att_skQ  : ∀ {ml}, derivable ml (sk iQ)

  -- NEW: The Bridge Rule (If you can derive m1, and m1 ≈ m2, you can derive m2)
  ---att_equiv : ∀ {ml m1 m2}, derivable ml m1 → m1 ≈ m2 → derivable ml m2

---notation ml " |> " m => AttackerModel.derivable ml m

--- typeclass resolution will automatically find the
--- right instance of `AttackerModel` when we write `ml |> m`
---variable [AttackerModel]


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
  -- convert Step.b1 1 [m3, m2, m1] ACtrl.a0 {session 0 ACtrl.a2 BCtrl.b1}
  --   (□⋄([m3, m2, m1] |> m3) ⋏ □⋄([m2, m1] |> m2) ⋏ □⋄(fst (dec m2 (sk iA)) ≈ nA 0) ⋏ □⋄(snd (snd (dec m2 (sk iA))) ≈ iB)
  --   ⋏ □⋄([m1] |> m1) ⋏ □⋄([] |> none) ⋏ mtrue)
  -- -- Subgoal 1: conf3
  -- · unfold conf3
  --   -- Evaluate the .ctrl record projection
  --   dsimp only
  --   -- Force both sides to explicitly use the `::ₘ` syntax
  --   change _ ::ₘ _ ::ₘ 0 = _ ::ₘ _ ::ₘ 0
  --   -- Now the swap will work perfectly
  --   rw [Multiset.cons_swap]

  -- -- Subgoal 2: conf4
  -- · ---unfold conf4
  --   dsimp only
  --   change _ ::ₘ _ ::ₘ 0 = _ ::ₘ _ ::ₘ 0
  --   rw [Multiset.cons_swap]

lemma trace : ∃ ml, (conf0 : Conf K) ~(ml)~>* conf4 := by
  use [Msg.none, m1, m2, m3]
  exact Trace.trans (Trace.step step1) <|
        Trace.trans (Trace.step step2) <|
        Trace.trans (Trace.step step3) <|
                    (Trace.step step4)

/-
lemma s_attack : snd (nB 0) ≈ iQ → ∃ st ml, (conf0 ~(ml)~>* st) ∧ st.cond ∧ st.chan |> nB 0 := by
  intro h_vuln
  obtain ⟨ml, h_trace⟩ := trace
  use conf4
  use ml
  refine ⟨h_trace, ?_, ?_⟩
  · unfold conf4
    simp [m1,m2,m3]
    --- TODO: just remove the nests
    refine ⟨⟨⟨AttackerModel.att_none, ?_⟩, ?_⟩, ?_⟩ <;> { apply AttackerModel.att_mem; simp }
  · -- The Attacker Derivation Phase
    unfold conf4
    -- Use `simp only` to evaluate the cryptography without reducing `fst (nB 0)` to `err`
    simp only [m1, m2, m3, m4, fst_pair_reduce, snd_pair_reduce, dec_enc_reduce]

    -- Step 1: Isolate m4 and swap its public key from pk(snd(nB 0)) to pk(iQ)
    have h_m4_eq : enc (pair (fst (nB 0)) (pair (nB 1) iB)) (r2 1) (pk (snd (nB 0))) ≈
                   enc (pair (fst (nB 0)) (pair (nB 1) iB)) (r2 1) (pk iQ) := by
      apply CompEquiv.enc_cong_pk
      exact h_vuln

    have h_derive_m4_iQ : [m4, m3, m2, m1] |> enc (pair (fst (nB 0)) (pair (nB 1) iB)) (r2 1) (pk iQ) := by
      apply AttackerModel.att_equiv (m1 := enc (pair (fst (nB 0)) (pair (nB 1) iB)) (r2 1) (pk (snd (nB 0))))
      · apply AttackerModel.att_mem
        -- Now there are no metavariables! simp will unfold m4, match it perfectly, and solve the goal.
        simp [m4, m3, m2, m1, fst_pair_reduce, snd_pair_reduce, dec_enc_reduce]
      · exact h_m4_eq

    -- Step 2: Decrypt it with the attacker's secret key to get the inner pair
    have h_inner : [m4, m3, m2, m1] |> pair (fst (nB 0)) (pair (nB 1) iB) :=
      AttackerModel.att_dec h_derive_m4_iQ AttackerModel.att_skQ

    -- Step 3: Extract the first half and pair it with the attacker's identity
    have h_fst : [m4, m3, m2, m1] |> fst (nB 0) := AttackerModel.att_fst h_inner
    have h_repaired : [m4, m3, m2, m1] |> pair (fst (nB 0)) iQ :=
      AttackerModel.att_pair h_fst AttackerModel.att_iQ

    -- Step 4: Prove that the repaired pair is equivalent to the target nonce (nB 0)
    apply AttackerModel.att_equiv h_repaired

    -- Goal: pair (fst (nB 0)) iQ ≈ nB 0
    apply CompEquiv.trans
    · apply CompEquiv.pair_cong_snd
      -- Flip h_vuln from `snd (nB 0) ≈ iQ` to `iQ ≈ snd (nB 0)`
      apply CompEquiv.symm
      exact h_vuln
    · -- Resolves `pair (fst (nB 0)) (snd (nB 0)) ≈ nB 0`
      apply CompEquiv.surj_pair
-/
---
--- MAIN THEOREM: computational lifting


/-
- Γ : conjuction of atomic propositions (of form ml |> m or m1 ≈ m2)
- Reach(ml, Γ) : my system can reach a state, where
  - Γ is the path condition, and
  - ml is the sequence of output messages (frame)
  - Reach(ml, Γ) may be regarded as atomic predicate,
    as it does not depend on possible worlds (really?)
- n : secret nonce
- φ* : The Fitting twist of φ in S4, where φ is FOL formula

Then my secrecy claim would be written in FOL as:
  secrecy : ∀ ml, Γ, (Reach(ml, Γ) ∧ Γ) → ¬(ml |> n)

Then, Fitting twists gives:
  secrecy* : ∀ ml, Γ, □((□⋄Reach(ml, Γ) ∧ Γ*) → □¬□⋄(ml |> n))
which is equivalent to:
  secrecy* : ∀ ml, Γ, □((Reach(ml, Γ) ∧ Γ*) → □¬□⋄(ml |> n))


-/





---
notation:20 w " ⊨ₛ₄ " p => p w

--- computational assumption. should be justified "computationally"
--- i.e.: ∃ (w : K.World), ∀ (w' : K.World), K.R w w' ∧ (snd (nB 0) ≈ iQ) w'
axiom ambiguity : K.root ⊨ₛ₄ ⋄□(snd (nB 0) ≈ iQ)

--- computational secrecy
--- Mᶜ ⊨ₛ₄ ϕ
--- iff Mᶜ, Ω ⊨ₛ₄ ϕ   (... by def. in the paper)
--- iff Mᶜ, S ⊨ₛ₄ ϕ for any S ⊆ Ω   (... need to show this)

--- computational attack is the negation
--- Mᶜ, S ⊨ₛ₄ ϕ for some S ⊆ Ω

--- computational attack follows from symbolic attack
--- (need to show this by initiality of the symbolic model)
--- A, S ⊨ₛ₄ ϕ for some S ⊆ Ω

axiom equiv_refl' : ∀ m, K.root ⊨ₛ₄ □⋄(m ≈ m)
axiom att_none' : ∀ {ml}, K.root ⊨ₛ₄ □⋄(ml |> none)
axiom att_mem' : ∀ {ml m}, m ∈ ml → (K.root ⊨ₛ₄ □⋄(ml |> m))

def leak :=
  ∃ st ml,
    (conf0 ~(ml)~>* st) ∧
    ∃ (w : K.World), (w ⊨ₛ₄ st.cond ⋏ □⋄(st.chan |> nB 0))


--- w r w' ∧ w ⊨ₛ₄ □⋄p → w ⊨ₛ₄ □⋄p
lemma persist_ow {K : KripkeFrame} {P : K.World → Prop} {w w' : K.World}
    (h_R : K.R w w') (h_boxdia : □⋄P w) : □⋄P w' := by
  intro v h_w'_v
  have h_w_v : K.R w v := K.trans h_R h_w'_v
  exact h_boxdia v h_w_v

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
  · -- rewrite nB 0 = <nQ, iQ> using axiom
    -- simp
    sorry









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
