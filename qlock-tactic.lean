import Bakery.DMC3
import Bakery.command


import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

import Lean
open Lean Meta Elab Command


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




def init : Pattern Conf := fun cf =>
  ∃ (i : Nat) (S : Multiset Nat),
    cf = ⟨ i ::ₘ S, ∅, ∅, List.nil ⟩
    ∧ Multiset.Nodup (i ::ₘ S)

/-- Recursively flattens a real Mathlib `Multiset.cons a (Multiset.cons b S)`
    into elements `[a, b]` and the base tail `S`. -/
partial def flattenMultiset (e : Expr) : Option (Expr × Expr) × List Expr × Expr :=
  let e := e.consumeMData
  match e with
  -- Matches exactly: `@Multiset.cons ?typeArg head tail`
  | .app (.app (.app (c@(.const ``Multiset.cons _)) typeArg) head) tail =>
      let (_, elems, finalTail) := flattenMultiset tail
      (some (c, typeArg), head :: elems, finalTail)
  | _ => (none, [], e)

/-- Rebuilds a Mathlib multiset Expr from an element list and a tail Expr. -/
def rebuildMultiset (consInfo : Expr × Expr) (elems : List Expr) (tail : Expr) : Expr :=
  let (consConst, typeArg) := consInfo
  elems.foldr (fun elem acc => mkApp3 consConst typeArg elem acc) tail

/--
  The core structural unifier.
  It takes a pattern, a target, and a dictionary of known variables.
  Returns `some new_dictionary` if successful, or `none` if unification fails.
-/
partial def myUnify (pat : Expr) (target : Expr) (env : NameMap Expr) : MetaM (Option (NameMap Expr)) := do
  -- Strip off hidden metadata (like source code positions) to expose the raw expression
  let pat := pat.consumeMData
  let target := target.consumeMData

  match pat, target with

  -- CASE 1: The pattern is a variable (e.g., `?i` or `?S`)
  | .mvar mId, _ =>
      let uniqueKey := mId.name

      match env.find? uniqueKey with
      | some boundExpr =>
          -- FIX: Do not use strict `==`. Recursively unify them to safely strip MData!
          myUnify boundExpr target env
      | none =>
          return some (env.insert uniqueKey target)

  -- CASE 1b: The target (right side) is a variable
  | _, .mvar mId =>
      let uniqueKey := mId.name

      match env.find? uniqueKey with
      | some boundExpr =>
          -- FIX: Recursively unify here as well
          myUnify boundExpr pat env
      | none =>
          return some (env.insert uniqueKey pat)

  -- AC-Matching Case (Backtracking Bipartite Matching Search)
  | e1@(.app (.app (.app (.const ``Multiset.cons _) _) _) _),
    e2@(.app (.app (.app (.const ``Multiset.cons _) _) _) _) =>

      -- A helper function to search one multiset for the head of another
      let doAC (srcElem srcTail dest : Expr) : MetaM (Option (NameMap Expr)) := do
        let (consInfoOpt, destElems, destTail) := flattenMultiset dest
        match consInfoOpt with
        | none => return none
        | some consInfo =>
            let rec search (rem : List Expr) (checked : List Expr) : MetaM (Option (NameMap Expr)) := do
              match rem with
              | [] => return none
              | tgt :: tgts =>
                  match ← myUnify srcElem tgt env with
                  | some env' =>
                      let remainingDest := rebuildMultiset consInfo (checked ++ tgts) destTail
                      match ← myUnify srcTail remainingDest env' with
                      | some finalEnv => return some finalEnv
                      | none => search tgts (checked ++ [tgt])
                  | none => search tgts (checked ++ [tgt])
            search destElems []

      -- Extract the heads and tails from both sides
      let .app (.app (.app _ _) patElem) patTail := e1 | return none
      let .app (.app (.app _ _) tgtElem) tgtTail := e2 | return none

      -- 1. Try driving the search from the Left (Pattern -> Target)
      match ← doAC patElem patTail e2 with
      | some finalEnv => return some finalEnv
      | none =>
          -- 2. If it fails, flip the perspective and drive from the Right! (Target -> Pattern)
          doAC tgtElem tgtTail e1

  -- CASE 2: Both are function applications (e.g., `Multiset.cons ?i ?S` and `Multiset.cons 5 ∅`)
  | .app patFn patArg, .app tgtFn tgtArg =>
      -- 1. Recursively unify the left side (the function)
      match ← myUnify patFn tgtFn env with
      | some env' =>
          -- 2. If successful, recursively unify the right side (the argument) with the updated dictionary
          myUnify patArg tgtArg env'
      | none =>
          return none

  -- CASE 3: Both are constants (e.g., `Conf.mk` and `Conf.mk`)
  | .const n1 _, .const n2 _ =>
      if n1 == n2 then return some env else return none

  -- CASE 4: Both are literals (e.g., the number `5` and `5`)
  | .lit l1, .lit l2 =>
      if l1 == l2 then return some env else return none

  -- CASE 5: Both are bound/free variables or types (fallback structural check)
  | .fvar f1, .fvar f2 => if f1 == f2 then return some env else return none
  | .bvar b1, .bvar b2 => if b1 == b2 then return some env else return none
  | .sort s1, .sort s2 => if s1 == s2 then return some env else return none



  -- BASE CASE: If none of the shapes match, unification fundamentally fails.
  | _, _ =>
      return none

/-- A custom command to test `myUnify` interactively. -/
elab "#test_unify " p:term " ~ " t:term : command => Command.liftTermElabM do
  -- 1. Parse the user's syntax into raw Expr trees without throwing errors on missing variables
  let pat ← Term.elabTerm p none
  let tgt ← Term.elabTerm t none

  -- 2. Run our custom unifier starting with an empty dictionary
  match ← myUnify pat tgt (Lean.mkNameMap Expr) with
  | some env =>
      logInfo "✅ Unification Succeeded! Dictionary:"
      for (uniqueKey, boundExpr) in env.toList do
        -- Convert the unique key back into a metadata object to check its name
        let mId : MVarId := { name := uniqueKey }
        let decl ← mId.getDecl
        let userName := decl.userName
        let exprStr ← ppExpr boundExpr

        -- We only want to print variables the user explicitly named (like ?x),
        -- ignoring Lean's messy invisible type variables.
        if !userName.isAnonymous && !userName.hasMacroScopes then
          logInfo m!"  {userName}  =>  {exprStr}"
  | none =>
      logInfo "❌ Unification Failed."

#test_unify  (?i :: ?S)  ~  (5 :: [1, 2, 3]) -- ✅
#test_unify  (?x, ∅)  ~  (10, ∅) -- ✅
#test_unify  (?i :: ?i :: ?S)  ~  (5 :: 10 :: [1]) -- ❌
#test_unify  (?i :: ?S)  ~  ∅ -- ❌
#test_unify  (?x, (∅ : List Nat))  ~  (10, (∅ : List Nat)) -- ✅
#test_unify  (10, (?y :: ?S))  ~  (10, (5 :: [1, 2])) -- ✅
#test_unify  (?i ::ₘ ?S)  ~  (5 ::ₘ ∅) -- ✅
#test_unify  (?i ::ₘ ?S)  ~  (5 ::ₘ 10 ::ₘ 20 ::ₘ ∅) -- ✅
#test_unify  (?i ::ₘ ?i ::ₘ ?S)  ~  (5 ::ₘ 10 ::ₘ ∅) -- ❌
#test_unify  (⟨(?i ::ₘ ?S) ∅ ∅ []⟩)  ~  (⟨(99 ::ₘ 1 ::ₘ ∅) ∅ ∅ []⟩) -- ✅

#test_unify  (1 :: ?L)  ~  (?L' :: [1, 2, 3]) -- ✅ (bidirectional unification)

#test_unify (5 ::ₘ ?i ::ₘ ∅)  ~  (10 ::ₘ 5 ::ₘ ∅) -- ✅
#test_unify (5 ::ₘ ?i)  ~  (10 ::ₘ 5 ::ₘ 0) -- ✅
#test_unify (?x ::ₘ ?x ::ₘ 0)  ~  (7 ::ₘ 7 ::ₘ 0) -- ✅
#test_unify (5 ::ₘ ∅) ~ (?x ::ₘ ∅) -- ✅
#test_unify (1 ::ₘ 2 ::ₘ ∅) ~ (2 ::ₘ ?y ::ₘ ∅) -- ✅
#test_unify (?x ::ₘ 2 ::ₘ ∅) ~ (1 ::ₘ ?y ::ₘ ∅) -- ✅
#test_unify (7 ::ₘ 7 ::ₘ ∅) ~ (?x ::ₘ ?x ::ₘ ∅) -- ✅
#test_unify (1 ::ₘ 2 ::ₘ ∅) ~ (2 ::ₘ ?S) -- ✅
#test_unify (1 ::ₘ ?S) ~ (3 ::ₘ 1 ::ₘ 2 ::ₘ ∅) -- ✅
#test_unify (3 ::ₘ 1 ::ₘ 2 ::ₘ ∅) ~ (1 ::ₘ ?S) -- ✅
#test_unify (?x ::ₘ 3 ::ₘ ∅) ~ (2 ::ₘ ?y ::ₘ ∅) -- ✅
#test_unify (1 ::ₘ 2 ::ₘ ∅) ~ (3 ::ₘ ?S) -- ❌

theorem n2w_applies_to_init (cf : Conf) (h : init cf) : ∃ cf', Step cf cf' := by
  unfold init at h

  obtain ⟨i, S, h_cf, h_nodup⟩ := h

  rw [h_cf]


  refine ⟨?new_state, ?_⟩
  · sorry
  · apply Step.n2w -- i'm here


  -- 3. Provide the exact next state to satisfy the existential quantifier (∃ cf').
  -- We know from `n2w` that `i` moves from the idle set to the waiting set,
  -- and is appended to the queue.
  use ⟨S, i ::ₘ ∅, ∅, [i]⟩

  -- 4. Apply the `n2w` constructor to close the goal.
  -- We explicitly pass the parameters: i, n=S, w=∅, c=∅, q=[].
  -- Lean's definitional equality automatically recognizes that `[] ++ [i]` is `[i]`.
  exact Step.n2w i S ∅ ∅ []



example (cf : Conf) (i : Nat) (S : Multiset Nat)
  (h_cf : cf = ⟨i ::ₘ S, ∅, ∅, []⟩) :
  ∃ cf', Step cf cf' :=

  -- The term mode proof:
  h_cf.symm ▸ ⟨⟨S, i ::ₘ ∅, ∅, [i]⟩, Step.n2w i S ∅ ∅ []⟩


/- pat1
  (< U:MSet | W:MSet | mt | Q:List >) s.t.
    (non-mt(U:MSet W:MSet) = tt)
    /\ (set(U:MSet W:MSet) = tt)
    /\ (l2ms(Q:List) = W:MSet))
-/
def pat1 : Pattern Conf := fun cf =>
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
def pat2 : Pattern Conf := fun cf =>
  ∃ (i : Nat) (V T : Multiset Nat) (Q' : List Nat),
    cf = ⟨ V, T, {i}, i :: Q' ⟩
    ∧ V + T + {i} ≠ ∅
    ∧ Multiset.Nodup (V + T + {i})
    ∧ ↑(i :: Q') = i ::ₘ T

def inv := pat1 ⊔ pat2
