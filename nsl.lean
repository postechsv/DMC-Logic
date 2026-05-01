import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.Group.Basic
---
--- giving computational semantics of CCSA as S4
---

axiom Box : Prop → Prop
prefix:75 "□" => Box
prefix:75 "◇" => fun p => ¬□(¬p)

--- system K = ax_K + ax_N
axiom ax_K {a b : Prop} : □(a → b) → (□a → □b) --- Distribution
axiom ax_N {a : Prop} : a → □a --- Necessitation

--- system S4 = system K + ax_T + ax_4
axiom ax_T {p : Prop} : □p → p --- Factivity
axiom ax_4 {p : Prop} : □p → □(□p) --- Positive Introspection

--- modus ponens for non-negligibility (only uses ax_K and ax_N)
lemma nnmp {p q : Prop} (h : p → q) (hp : ◇□p) : ◇□q := by
  -- hp is ¬□(¬□p), and our goal is ¬□(¬□q)
  intro h_contra
  -- 1. Necessitate the local implication and distribute with K
  have h1 : □p → □q := ax_K (ax_N h)
  -- 2. Take the contrapositive of the lifted implication
  have h2 : ¬□q → ¬□p := fun hnq hp_inner => hnq (h1 hp_inner)
  -- 3. Necessitate the contrapositive and distribute with K again
  have h3 : □(¬□q → ¬□p) := ax_N h2
  have h4 : □(¬□q) → □(¬□p) := ax_K h3
  -- 4. Derive □(¬□p) using our contradictory assumption, which contradicts hp
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
  --- assymetric encryption scheme
  | enc  : Msg -> Msg -> Msg -> Msg
  ---| dec  : Msg -> Msg -> Msg
  | pk   : Msg -> Msg
  | sk   : Msg -> Msg
  --- pairing
  | pair : Msg -> Msg -> Msg
  ---| fst  : Msg -> Msg
  ---| snd  : Msg -> Msg
  deriving DecidableEq
open Msg

--- equational axioms for pairing and encryption
---axiom fst_pair : ∀ m1 m2, fst (pair m1 m2) = m1
---axiom snd_pair : ∀ m1 m2, snd (pair m1 m2) = m2
---axiom dec_enc : ∀ m r id, dec (enc m r (pk id)) (sk id) = m
-- Define the destructors as actual computable functions!
@[simp]
def fst : Msg → Msg
  | pair m1 _ => m1
  | _ => err

@[simp]
def snd : Msg → Msg
  | pair _ m2 => m2
  | _ => err

@[simp]
def dec : Msg → Msg → Msg
  | enc m _ (pk id1), sk id2 =>
      if id1 = id2 then m else err
  | _, _ => err


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

notation ml " |> " m => AttackerModel.derivable ml m

--- typeclass resolution will automatically find the
--- right instance of `AttackerModel` when we write `ml |> m`
variable [AttackerModel]


--- caveat: att is not restricted to be a PPTM
---def derivable (ml : List Msg) (m : Msg) : Prop := True
---∃ att : List Msg → Msg, att ml = m
---notation ml " |> " m => derivable ml m


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
inductive Step : Conf → Conf → Prop where
  | a1 (i : Nat) (x : Msg) : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step { chan := ml, ctrl := {session i ACtrl.a0 cB} + ss, cond := p }
           { chan := (enc (pair (nA i) iA) (r1 i) (pk iB)) :: ml,
             ctrl := {session i ACtrl.a1 cB} + ss,
             cond := p ∧ (ml |> x) }
  | a2 (i : Nat) (x : Msg) : ∀ ml : List Msg, ∀ cB : BCtrl, ∀ ss : Multiset Session, ∀ p : Prop,
      Step { chan := ml, ctrl := {session i ACtrl.a1 cB} + ss, cond := p }
           { chan := (enc (fst (snd (dec x (sk iA)))) (r3 i) (pk iB)) :: ml,
             ctrl := {session i ACtrl.a2 cB} + ss,
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
         /\ ([m2, m1] |> m2) /\ fst (dec m2 (sk iA)) = nA 0 ∧ snd (snd (dec m2 (sk iA))) = iB }

--- output of b1
def m4 : Msg := (enc (pair (fst (dec m3 (sk iB))) (pair (nB 1) iB))
                     (r2 1) (pk (snd (dec m3 (sk iB)))))

def conf4 : Conf :=
  { chan := [m4, m3, m2, m1],
    ctrl := {session 0 ACtrl.a2 BCtrl.b1, session 1 ACtrl.a0 BCtrl.b1},
    cond := (((True /\ ([] |> none)) /\ ([m1] |> m1))
         /\ ([m2, m1] |> m2) /\ fst (dec m2 (sk iA)) = nA 0 ∧ snd (snd (dec m2 (sk iA))) = iB)
         /\ ([m3, m2, m1] |> m3) }

example : conf0 ⇒* conf0 := by
  apply Relation.ReflTransGen.refl

lemma step1 : conf0 ⇒ conf1 := by
  apply Step.a1 0 none [] BCtrl.b0 {session 1 ACtrl.a0 BCtrl.b0} True

lemma step2 : conf1 ⇒ conf2 := by
  apply Step.b1 0 m1 [m1] ACtrl.a1 {session 1 ACtrl.a0 BCtrl.b0} (True /\ ([] |> none))

lemma step3 : conf2 ⇒ conf3 := by
  apply Step.a2 0 m2 [m2, m1] BCtrl.b1 {session 1 ACtrl.a0 BCtrl.b0}
                              ((True /\ ([] |> none)) /\ ([m1] |> m1))

lemma step4 : conf3 ⇒ conf4 := by
  convert Step.b1 1 m3 [m3, m2, m1] ACtrl.a0 {session 0 ACtrl.a2 BCtrl.b1}
    (((True /\ ([] |> none)) /\ ([m1] |> m1)) /\ ([m2, m1] |> m2) /\ fst (dec m2 (sk iA)) = nA 0 ∧ snd (snd (dec m2 (sk iA))) = iB)

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

lemma trace : conf0 ⇒* conf4 := by
  apply Relation.ReflTransGen.head step1
  apply Relation.ReflTransGen.head step2
  apply Relation.ReflTransGen.head step3
  apply Relation.ReflTransGen.head step4
  apply Relation.ReflTransGen.refl


--- attack in the "symbolic world"
lemma s_attack : fst (nB 0) = iQ → ∃ st, conf0 ⇒* st ∧ st.cond ∧ st.chan |> nB 0 := by
  intro h_vuln
  use conf4
  refine ⟨trace, ?_, ?_⟩
  · unfold conf4
    simp [m1,m2,m3]
  · unfold conf4
    simp
    exact ⟨fun _ => nB 0, rfl⟩


--- computational assumption
axiom nneq0 : fst (nB 0) = iQ --- should be justified "computationally"

--- lifting symbolic attack to computational attack (attack preservation)
lemma c_attack : ◇□ ∃ st, conf0 ⇒* st ∧ st.cond ∧ st.chan |> nB 0 := by
  have h_modal_axiom : ◇□ (fst (nB 0) = iQ) := by
    have h_box := ax_N nneq0
    intro h_contra
    exact (ax_T h_contra) h_box
  exact nnmp s_attack h_modal_axiom
