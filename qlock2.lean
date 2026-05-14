import Bakery.DMC3

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

import Lean



structure Conf where
  n : Multiset Nat
  w : Multiset Nat
  c : Multiset Nat
  q : List Nat

instance : State Conf := ⟨⟩



inductive Step : Transition Conf where
  -- n2w:    ⟨ n i | w | c | q ⟩     →    ⟨ n | w i | c | q ; i ⟩
  | n2w : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step
        ⟨ i ::ₘ n, w, c, q ⟩
        ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

  -- w2c:  ⟨ n | w i | c | i ; q ⟩   →    ⟨ n | w | c i | i ; q ⟩
  | w2c : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step ⟨ n, i ::ₘ w, c, i :: q ⟩ ⟨ n, w, i ::ₘ c, i :: q ⟩

  -- c2n:  ⟨ n | w | c i | i ; q ⟩   →    ⟨ n i | w | c | q ⟩
  | c2n : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step ⟨ n, w, i ::ₘ c, i :: q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

  -- **join**:   ⟨ n | w | c | q ⟩       →    ⟨ n **i** | w | c | q ⟩  if ¬ dupl(n i w c)
  | join : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      (i ∉ n + w + c) →
      Step ⟨ n, w, c, q ⟩ ⟨ i ::ₘ n, w, c, q ⟩

  -- exit:   ⟨ n i | w | c | q ⟩     →    ⟨ n | w | c | q ⟩
  | exit : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      Step ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, w, c, q ⟩


-- Define each step completely in isolation
inductive step_n2w : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_n2w ⟨ i ::ₘ n, w, c, q ⟩ ⟨ n, i ::ₘ w, c, q ++ [i] ⟩

inductive step_w2c : Transition Conf where
  | mk : ∀ (i : Nat) (n w c : Multiset Nat) (q : List Nat),
      step_w2c ⟨ n, i ::ₘ w, c, i :: q ⟩ ⟨ n, w, i ::ₘ c, i :: q ⟩

-- ... (do this for c2n, join, and exit) ...

-- Now compose your system algebraically!
def BakeryStep : Transition Conf :=
  step_n2w ⊔ step_w2c ⊔ step_c2n ⊔ step_join ⊔ step_exit

--- DMC: Define the System instance for Conf
instance : System Conf := ⟨Step⟩



open Lean Meta Elab Command Term

-- 1. Define the syntax for your new command
syntax (name := nextStatesCmd) "#next_states " term : command

-- 2. Write the Elaborator (the actual code that runs when you type the command)
@[command_elab nextStatesCmd]
def elabNextStates : CommandElab := fun stx => do
  match stx with
  | `(command| #next_states $st) =>
    -- We transition from the Command monad to the Term elaboration monad
    liftTermElabM do
      -- Step A: Convert the user's syntax into a formal Lean Expression (Expr)
      let currentState ← elabTerm st none

      -- Step B: List the constructors of your Step relation
      -- (The double backticks `` resolve the exact name in the environment)
      let constructors := [``Step.n2w, ``Step.w2c, ``Step.c2n, ``Step.join, ``Step.exit]
      let mut foundOne := false

      logInfo m!"Exploring next states for:\n{currentState}\n---"

      -- Step C: Iterate through each transition rule
      for ctorName in constructors do
        -- We run each attempt in a fresh metavariable context so failed
        -- unifications don't pollute the next attempt.
        let success ← withNewMCtxDepth do
          let ctorInfo ← getConstInfo ctorName

          -- MAGIC HAPPENS HERE: forallMetaTelescope takes a type like
          -- `∀ (i : Nat) (n w c : Multiset Nat) ..., Step lhs rhs`
          -- and strips away the `∀`, replacing i, n, w, c with fresh metavariables.
          let (_, _, type) ← forallMetaTelescope ctorInfo.type

          -- We check if the resulting type is exactly `Step ?lhs ?rhs`
          if type.isAppOfArity ``Step 2 then
            -- Extract the ?lhs and ?rhs metavariables from the AST
            let lhs := type.appFn!.appArg!
            let rhs := type.appArg!

            -- UNIFICATION: We ask Lean, "Can the user's state equal this rule's LHS?"
            if ← isDefEq currentState lhs then
              -- If yes, Lean automatically binds all the variables!
              -- We just instantiate the RHS to see what it calculated.
              let nextState ← instantiateMVars rhs
              logInfo m!"🔥 Rule [{ctorName}] applies!\nNext State: {nextState}\n"
              return true
          return false

        if success then foundOne := true

      if !foundOne then
        logInfo "No valid transitions. This is a terminal state (or a deadlock!)."

  | _ => throwUnsupportedSyntax

#next_states (⟨ 1 ::ₘ 0, 2 ::ₘ 0, 0, [2] ⟩ : Conf)

#next_states (⟨ 99 ::ₘ ?N, ?W, ?C, ?Q ⟩ : Conf)




def init (cf : Conf) : Prop :=
  ∃ (i : Nat) (S : Multiset Nat),
    cf = ⟨ i ::ₘ S, ∅, ∅, List.nil ⟩
    ∧ Multiset.Nodup (i ::ₘ S)

/- pred1
  (< U:MSet | W:MSet | mt | Q:List >) s.t.
    (non-mt(U:MSet W:MSet) = tt)
    /\ (set(U:MSet W:MSet) = tt)
    /\ (l2ms(Q:List) = W:MSet))
-/
def pred1 (cf : Conf) : Prop :=
  ∃ (U W : Multiset Nat) (Q : List Nat),
    cf = ⟨ U, W, ∅, Q ⟩
    ∧ U + W ≠ ∅
    ∧ Multiset.Nodup (U + W)
    ∧ ↑Q = W

/- pred2
  (< V:MSet | T:MSet | i:Nat | i:Nat ; Q':List >) s.t.
    (non-mt(V:MSet T:MSet i:Nat) = tt)
    /\ (set(V:MSet T:MSet i:Nat) = tt)
    /\ (l2ms(i:Nat ; Q':List) = T:MSet i:Nat))
-/
def pred2 (cf : Conf) : Prop :=
  ∃ (i : Nat) (V T : Multiset Nat) (Q' : List Nat),
    cf = ⟨ V, T, {i}, i :: Q' ⟩
    ∧ V + T + {i} ≠ ∅
    ∧ Multiset.Nodup (V + T + {i})
    ∧ ↑(i :: Q') = i ::ₘ T

def inv (cf : Conf) : Prop := pred1 cf ∨ pred2 cf

#check (pred1 : Pattern Conf) -- Conf → Prop
#check (pred2 : Pattern Conf) -- Conf → Prop
#check (inv : Pattern Conf)   -- Conf → Prop


lemma inv_ind : (↑Step : Transformer Conf) inv inv := sorry
lemma inv_init : (stepUp Step) init inv := sorry

-- ⟨ 1 ::ₘ 0 , ∅, ∅, List.nil ⟩ => ⟨ {0}, {1}, ∅, [1] ⟩
def cf0 (cf : Conf) : Prop := cf = ⟨ 1 ::ₘ 0 , ∅, ∅, List.nil ⟩
def cf1 (cf : Conf) : Prop := cf = ⟨ {0}, {1}, ∅, [1] ⟩

lemma step_0_1 : PStep Conf ⟨cf0⟩ ⟨cf1⟩ := by

  sorry

--lemma step1 : ⟨ 1 ::ₘ 0 , ∅, ∅, List.nil ⟩ => ⟨ {0}, {1}, ∅, [1] ⟩

-- pattern lifting for states
def state2pat (cf : Conf) : Pattern Conf := sorry


lemma trace : ∃ cf cf', PStep Conf (state2pat cf) (state2pat cf') := sorry
