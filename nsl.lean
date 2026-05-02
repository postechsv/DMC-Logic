import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.Group.Basic

axiom Box : Prop → Prop
prefix:75 "□" => Box
prefix:75 "◇" => fun p => ¬□(¬p)

--- system K = ax_K + ax_N
axiom ax_K {a b : Prop} : □(a → b) → (□a → □b) --- Distribution
axiom ax_N {a : Prop} : a → □a --- Necessitation

--- system S4 = system K + ax_T + ax_4
axiom ax_T {p : Prop} : □p → p --- Factivity
axiom ax_4 {p : Prop} : □p → □(□p) --- Positive Introspection


lemma nnmp {p q : Prop} (h : □(p → q)) (hp : ◇□p) : ◇□q := by
  -- hp is ¬□(¬□p), and our goal is ¬□(¬□q)
  intro h_contra
  -- Now we don't need to illegally necessitate a local variable.
  -- We already have h : □(p → q). We just distribute it with ax_K.
  have h1 : □p → □q := ax_K h

  -- The rest of the proof is identical to your original one!
  have h2 : ¬□q → ¬□p := fun hnq hp_inner => hnq (h1 hp_inner)
  have h3 : □(¬□q → ¬□p) := ax_N h2
  -- (Note: This is still a bit of a hack in your shallow embedding, but acceptable for now)
  have h4 : □(¬□q) → □(¬□p) := ax_K h3
  have h5 : □(¬□p) := h4 h_contra
  exact hp h5

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
class CompEquiv where
  equiv : Msg → Msg → Prop
  refl  : ∀ m, equiv m m
  --- You can add symm and trans here later if your proofs require them
  symm  : ∀ m1 m2, equiv m1 m2 → equiv m2 m1
  trans : ∀ m1 m2 m3, equiv m1 m2 → equiv m2 m3 → equiv m1 m3

  -- The core of your insight: re-pairing halves yields the original
  surj_pair : ∀ {m}, equiv (pair (fst m) (snd m)) m
  -- Congruence rules for rewriting
  pair_cong_snd : ∀ {m1 m2 m3}, equiv m2 m3 → equiv (pair m1 m2) (pair m1 m3)
  enc_cong_pk   : ∀ {m r k1 k2}, equiv k1 k2 → equiv (enc m r (pk k1)) (enc m r (pk k2))

infix:50 " ≈ " => CompEquiv.equiv

variable [CompEquiv]

--- This is the magic line. It tells `simp` that anytime it sees `X ≈ X`,
--- it can instantly reduce it to `True`, mimicking strict equality.
@[simp]
lemma CompEquiv_refl {m : Msg} : m ≈ m := CompEquiv.refl m




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
  att_equiv : ∀ {ml m1 m2}, derivable ml m1 → m1 ≈ m2 → derivable ml m2

notation ml " |> " m => AttackerModel.derivable ml m

--- typeclass resolution will automatically find the
--- right instance of `AttackerModel` when we write `ml |> m`
variable [AttackerModel]


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

--- global state
structure Conf where
  chan : List Msg
  ctrl : Multiset Session --- caveat: can only have finite number of sessions
  cond : Prop --- guard condition

--- transition relation
inductive Step (x : Msg) : Conf → Conf → Prop where
  | a1 (i : Nat)  : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step x
        { chan := ml, ctrl := {session i ACtrl.a0 cB} + ss, cond := p }
        { chan := (enc (pair (nA i) iA) (r1 i) (pk iB)) :: ml,
          ctrl := {session i ACtrl.a1 cB} + ss,
          cond := p ∧ (ml |> x) }
  | a2 (i : Nat) : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step x
        { chan := ml, ctrl := {session i ACtrl.a1 cB} + ss, cond := p }
        { chan := (enc (fst (snd (dec x (sk iA)))) (r3 i) (pk iB)) :: ml,
          ctrl := {session i ACtrl.a2 cB} + ss,
          cond := p ∧ (ml |> x) ∧ fst (dec x (sk iA)) ≈ nA i ∧ snd (snd (dec x (sk iA))) ≈ iB }
  | b1 (i : Nat) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step x
        { chan := ml, ctrl := {session i cA BCtrl.b0} + ss, cond := p }
        { chan := (enc (pair (fst (dec x (sk iB))) (pair (nB i) iB))
                      (r2 i) (pk (snd (dec x (sk iB))))) :: ml,
          ctrl := {session i cA BCtrl.b1} + ss,
          cond := p ∧ (ml |> x) }
  | b2 (i : Nat) : ∀ ml : List Msg, ∀ cA : ACtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step x
        { chan := ml, ctrl := {session i cA BCtrl.b1} + ss, cond := p }
        { chan := ok i :: ml,
          ctrl := {session i cA BCtrl.b2} + ss,
          cond := p ∧ (ml |> x) ∧ dec x (sk iB) ≈ nB i }

notation:110 st1 " ~(" x ")~> " st2 => Step x st1 st2

-- Labeled Reflexive-Transitive Closure
inductive Trace : List Msg → Conf → Conf → Prop where
  | refl (st : Conf) : Trace [] st st
  | step {st1 st2 : Conf} {x : Msg} :
      Step x st1 st2 →
      Trace [x] st1 st2
  | trans {st1 st2 st3 : Conf} {xl1 xl2 : List Msg} :
      Trace xl1 st1 st2 →
      Trace xl2 st2 st3 →
      Trace (xl1 ++ xl2) st1 st3

-- Notation: Multi-step transition from st1 to st2, labeled with sequence xl
notation:110 st1 " ~(" xl ")~>* " st2 => Trace xl st1 st2

---
--- constructing the symbolic attack
---

def conf0 : Conf := { chan := [],
                      ctrl := {session 0 ACtrl.a0 BCtrl.b0, session 1 ACtrl.a0 BCtrl.b0},
                      cond := True }

--- output of a1
def m1 : Msg := enc (pair (nA 0) iA) (r1 0) (pk iB)

def conf1 : Conf :=
  { chan := [m1],
    ctrl := {session 0 ACtrl.a1 BCtrl.b0, session 1 ACtrl.a0 BCtrl.b0},
    cond := True /\ [] |> none }

--- output of b1
def m2 : Msg := (enc (pair (fst (dec m1 (sk iB))) (pair (nB 0) iB))
                     (r2 0) (pk (snd (dec m1 (sk iB)))))

def conf2 : Conf :=
  { chan := [m2, m1],
    ctrl := {session 0 ACtrl.a1 BCtrl.b1, session 1 ACtrl.a0 BCtrl.b0},
    cond := (True /\ ([] |> none)) /\ ([m1] |> m1) }
--- careful on assoc of /\ : lean's unification doesn't handle /\'s associativity
--- (caught by gemini)

--- output of a2
def m3 : Msg := (enc (fst (snd (dec m2 (sk iA)))) (r3 0) (pk iB))

def conf3 : Conf :=
  { chan := [m3, m2, m1],
    ctrl := {session 0 ACtrl.a2 BCtrl.b1, session 1 ACtrl.a0 BCtrl.b0},
    cond := ((True /\ ([] |> none)) /\ ([m1] |> m1))
         /\ ([m2, m1] |> m2) /\ fst (dec m2 (sk iA)) ≈ nA 0 ∧ snd (snd (dec m2 (sk iA))) ≈ iB }

--- output of b1
def m4 : Msg := (enc (pair (fst (dec m3 (sk iB))) (pair (nB 1) iB))
                     (r2 1) (pk (snd (dec m3 (sk iB)))))

def conf4 : Conf :=
  { chan := [m4, m3, m2, m1],
    ctrl := {session 0 ACtrl.a2 BCtrl.b1, session 1 ACtrl.a0 BCtrl.b1},
    cond := (((True /\ ([] |> none)) /\ ([m1] |> m1))
         /\ ([m2, m1] |> m2) /\ fst (dec m2 (sk iA)) ≈ nA 0 ∧ snd (snd (dec m2 (sk iA))) ≈ iB)
         /\ ([m3, m2, m1] |> m3) }

example : conf0 ~([])~>* conf0 := by
  apply Trace.refl

lemma step1 : conf0 ~(Msg.none)~> conf1 := by
  apply Step.a1 0 [] BCtrl.b0 {session 1 ACtrl.a0 BCtrl.b0} True

lemma step2 : conf1 ~(m1)~> conf2 := by
  apply Step.b1 0 [m1] ACtrl.a1 {session 1 ACtrl.a0 BCtrl.b0} (True /\ ([] |> none))

lemma step3 : conf2 ~(m2)~> conf3 := by
  apply Step.a2 0 [m2, m1] BCtrl.b1 {session 1 ACtrl.a0 BCtrl.b0} _
  use m2
  apply Step.a2 0 [m2, m1] BCtrl.b1 {session 1 ACtrl.a0 BCtrl.b0}
                              ((True /\ ([] |> none)) /\ ([m1] |> m1))

lemma step4 : conf3 ~(m3)~> conf4 := by
  convert Step.b1 1 [m3, m2, m1] ACtrl.a0 {session 0 ACtrl.a2 BCtrl.b1}
    (((True /\ ([] |> none)) /\ ([m1] |> m1)) /\ ([m2, m1] |> m2) /\ fst (dec m2 (sk iA)) ≈ nA 0 ∧ snd (snd (dec m2 (sk iA))) ≈ iB)

  -- Subgoal 1: conf3
  · unfold conf3
    -- Evaluate the .ctrl record projection
    dsimp only
    -- Force both sides to explicitly use the `::ₘ` syntax
    change _ ::ₘ _ ::ₘ 0 = _ ::ₘ _ ::ₘ 0
    -- Now the swap will work perfectly
    rw [Multiset.cons_swap]

  -- Subgoal 2: conf4
  · unfold conf4
    dsimp only
    change _ ::ₘ _ ::ₘ 0 = _ ::ₘ _ ::ₘ 0
    rw [Multiset.cons_swap]

lemma trace : ∃ ml, conf0 ~(ml)~>* conf4 := by
  use [Msg.none, m1, m2, m3]
  have t1 : Trace [Msg.none] conf0 conf1 := Trace.step step1
  have t2 : Trace [m1] conf1 conf2 := Trace.step step2
  have t3 : Trace [m2] conf2 conf3 := Trace.step step3
  have t4 : Trace [m3] conf3 conf4 := Trace.step step4
  have t12 := Trace.trans t1 t2
  have t34 := Trace.trans t3 t4
  exact Trace.trans t12 t34

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

---
--- MAIN THEOREM: computational lifting
---

--- computational assumption
axiom ambiguity : ◇□ (snd (nB 0) ≈ iQ) --- should be justified "computationally"

--- lifting symbolic attack to computational attack (attack preservation)
theorem c_attack : ◇□ ∃ st ml, (conf0 ~(ml)~>* st) ∧ st.cond ∧ st.chan |> nB 0 := by
  exact nnmp (ax_N s_attack) ambiguity
