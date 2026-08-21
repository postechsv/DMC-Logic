import Lean


namespace framework

universe u v w x

-- α is the type of states
class State (α : Type u) : Prop where

-- P is a type of atomic patterns denoting sets of α-states.
class AtPattern (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

instance {α : Type u} [State α] : AtPattern α (α × Prop) where
  semantics p state := p.fst = state ∧ p.snd

-- A model value is an atomic pattern matching exactly that value.
instance {α : Type u} [State α] : AtPattern α α where
  semantics p state := p = state

instance {α : Type u} {A : Type v} {P : Type w}
    [State α] [AtPattern α P] : AtPattern α (A → P) where
  semantics p state := ∃ x, AtPattern.semantics (p x) state

def Unifiable {α : Type u} {P : Type v} {Q : Type w}
    [State α] [AtPattern α P] [AtPattern α Q]
    (p : P) (q : Q) : Prop :=
  ∃ state, AtPattern.semantics p state ∧ AtPattern.semantics q state

infix:50 " ⋈ " => Unifiable

end framework


namespace ex2

-- f(x1, x2) = f(f(y1, y2), c)
-- x1 = f(u1, u2)
-- x2 = c
-- y1 = u1
-- y2 = u2

inductive Term where
  | c : Term
  | f : Term → Term → Term
  deriving Repr

open Term




def pat1 (x1 x2 : Term) : Term :=
  f x1 x2
#print pat1

def pat2 (y1 y2 : Term) : Term :=
  f (f y1 y2) c
#print pat2


-- ALL original pattern variables are implicit holes.
def compute_uniform_unifiers {x1 x2 y1 y2 : Term}
  (eq : pat1 x1 x2 = pat2 y1 y2) :
  Term × Term × Term × Term :=
  (x1, x2, y1, y2)

-- We introduce the fresh basis variables u1 and u2.
-- We explicitly bind the independent variables (y1, y2) to the basis.
-- We pass `rfl`, forcing Lean to compute the dependent variables (x1, x2).
def uniform_mgu (u1 u2 : Term) :=
  compute_uniform_unifiers (y1 := u1) (y2 := u2) rfl

#reduce uniform_mgu


/--
  All three variables are implicit holes.
  The equation is beautifully cross-coupled.
-/
def compute_ground_mgu {x1 y1 y2 : Term}
  (eq : f x1 (f c y2) = f (f y1 c) x1) :
  Term × Term × Term :=
  (x1, y1, y2)

-- Lean's unifier cascades through the substitutions automatically.
def ground_mgu := compute_ground_mgu rfl

#reduce ground_mgu
-- (Term.f Term.c Term.c, Term.c, Term.c)


end ex2


namespace free_unification

open Lean Meta Elab Term Tactic
open framework

-- 1. Standard Domain AST (No 'var' constructor needed)
inductive Conf where
  | c : Conf
  | f : Conf → Conf → Conf
  deriving Repr
instance : State Conf := ⟨⟩
open Conf





private structure SaturatedPattern where
  application : Expr
  arguments : Array Expr
  argumentNames : Array Name

private def saturatePattern (pattern : Expr) : MetaM SaturatedPattern := do
  let type ← inferType pattern
  let (arguments, binderInfos, _) ← forallMetaTelescopeReducing type
  unless binderInfos.all fun info => info == .default do
    throwError "prototype `unify` only supports explicit pattern arguments"
  let mut argumentNames := #[]
  for argument in arguments do
    let decl ← argument.mvarId!.getDecl
    argumentNames := argumentNames.push decl.userName.eraseMacroScopes
  return {
    application := mkAppN pattern arguments
    arguments
    argumentNames
  }

private structure NativeUnification where
  lhs : SaturatedPattern
  rhs : SaturatedPattern
  unifiable : Bool
  templates : Array Expr := #[]
  residuals : Array MVarId := #[]

private def nativeUnify (lhs rhs : Expr) : MetaM NativeUnification := do
  let lhs ← saturatePattern lhs
  let rhs ← saturatePattern rhs
  let unifiable ← isDefEq lhs.application rhs.application
  if !unifiable then
    return { lhs, rhs, unifiable }
  let originalArguments := lhs.arguments ++ rhs.arguments
  let mut templates := #[]
  let mut residuals := #[]
  for argument in originalArguments do
    let template ← instantiateMVars argument
    templates := templates.push template
    for residual in ← getMVars template do
      unless residuals.contains residual do
        residuals := residuals.push residual
  for residual in residuals do
    unless originalArguments.any fun argument =>
        argument.isMVar && argument.mvarId! == residual do
      throwError "native unifier introduced an unexpected metavariable"
  return { lhs, rhs, unifiable, templates, residuals }

private def replaceResiduals
    (template : Expr) (residuals : Array MVarId)
    (basis : Array Expr) : Expr :=
  template.replace fun subterm =>
    match subterm with
    | .mvar id =>
        match residuals.idxOf? id with
        | some i => basis[i]?
        | none => none
    | _ => none

private def visibleName (fallback : String) (name : Name) : Name :=
  if name.isAnonymous then Name.mkSimple fallback else name.eraseMacroScopes

private def freshVisibleIdent (ref : Syntax) (base : Name) : TacticM Ident := do
  let goal ← getMainGoal
  let name ← goal.withContext do
    return (← getLCtx).getUnusedName base
  return mkIdentFrom ref name

private def assertBySimpAll
    (name : Name) (type : Expr) : TacticM FVarId := do
  let goal ← getMainGoal
  let (proof, fvarId, nextGoal) ← goal.withContext do
    let proof ← mkFreshExprMVar (some type)
    let (fvarId, nextGoal) ← goal.note name proof (some type)
    return (proof, fvarId, nextGoal)
  replaceMainGoal [proof.mvarId!]
  evalTactic (← `(tactic| simp_all))
  unless ← proof.mvarId!.isAssigned do
    throwError "failed to prove unifier equation `{name}`"
  setGoals [nextGoal]
  return fvarId

/--
Proof-of-concept free-unification tactic.  It saturates both arbitrary pattern
functions with fresh metavariables and delegates computation of the MGU and
its residual basis variables to `Lean.Meta.isDefEq`.  The semantic hypothesis
is then decomposed to obtain proof-level variables and a constructor equality;
the native substitution is exposed as one checked equation per original
variable.
-/
elab "unify " h:ident : tactic => do
  let originalHId ← getFVarId h
  let originalHType ← instantiateMVars (← originalHId.getType)
  let typeArgs := originalHType.getAppArgs
  unless originalHType.getAppFn.isConstOf ``Unifiable && typeArgs.size >= 2 do
    throwErrorAt h "expected a hypothesis of the form `p ⋈ q`"
  let lhsExpr := typeArgs[typeArgs.size - 2]!
  let rhsExpr := typeArgs[typeArgs.size - 1]!
  let initialGoal ← getMainGoal
  let native ← initialGoal.withContext do nativeUnify lhsExpr rhsExpr

  -- Decompose the semantics, retaining the actual values chosen for every
  -- pattern argument and the two equalities with the common state.
  let stateIdent ← freshVisibleIdent h.raw `_unifyState
  let hpIdent ← freshVisibleIdent h.raw `_unifyLhs
  let hqIdent ← freshVisibleIdent h.raw `_unifyRhs
  evalTactic (← `(tactic|
    rcases ($h:term) with
      ⟨$stateIdent:ident, $hpIdent:ident, $hqIdent:ident⟩))

  let mut actualIdents := #[]
  for i in [:native.lhs.arguments.size] do
    let base := visibleName s!"x{i + 1}" native.lhs.argumentNames[i]!
    let argumentIdent ← freshVisibleIdent h.raw base
    evalTactic (← `(tactic|
      rcases ($hpIdent:term) with ⟨$argumentIdent:ident, $hpIdent:ident⟩))
    actualIdents := actualIdents.push argumentIdent
  for i in [:native.rhs.arguments.size] do
    let base := visibleName s!"y{i + 1}" native.rhs.argumentNames[i]!
    let argumentIdent ← freshVisibleIdent h.raw base
    evalTactic (← `(tactic|
      rcases ($hqIdent:term) with ⟨$argumentIdent:ident, $hqIdent:ident⟩))
    actualIdents := actualIdents.push argumentIdent

  let actualIds ← actualIdents.mapM getFVarId
  let actualValues := actualIds.map mkFVar
  let hpId ← getFVarId hpIdent
  let hqId ← getFVarId hqIdent

  -- Turn the two equalities with the common state into one reduced equality
  -- between constructor applications.  This is the proof certificate used by
  -- `simp_all` below; native unification itself is never trusted as a proof.
  let equalityName := `_unifyEq
  let goal ← getMainGoal
  let (equalityType, equalityProof) ← goal.withContext do
    let hqSymm ← mkAppM ``Eq.symm #[mkFVar hqId]
    let proof ← mkAppM ``Eq.trans #[mkFVar hpId, hqSymm]
    let proofType ← whnf (← inferType proof)
    let some (_, lhs, rhs) := proofType.eq?
      | throwError "malformed atomic-pattern semantics"
    let lhs ← withTransparency .all <| whnf lhs
    let rhs ← withTransparency .all <| whnf rhs
    return (← mkEq lhs rhs, proof)
  let (_, goal) ← goal.withContext do
    goal.note equalityName equalityProof (some equalityType)
  setGoals [goal]

  if !native.unifiable then
    try
      evalTactic (← `(tactic| solve | simp_all))
    catch _ =>
      throwErrorAt h
        "native unification failed, but this prototype could not certify the failure"
    return

  let symbolicArguments := native.lhs.arguments ++ native.rhs.arguments
  let mut basisValues := #[]
  let mut basisEquationIds : Array (Option FVarId) :=
    Array.replicate actualValues.size none

  -- Each residual native metavariable is one free basis parameter.  Generalize
  -- the corresponding concrete witness so the user receives an ordinary Lean
  -- variable `uN`, not an object-language variable constructor or metavariable.
  for basisIndex in [:native.residuals.size] do
    let residual := native.residuals[basisIndex]!
    let some originalIndex := symbolicArguments.findIdx? fun argument =>
        argument.isMVar && argument.mvarId! == residual
      | throwError "residual metavariable is not an original pattern variable"
    let uIdent ← freshVisibleIdent h.raw <| Name.mkSimple s!"u{basisIndex + 1}"
    let equationIdent ← freshVisibleIdent h.raw <|
      Name.mkSimple s!"h{originalIndex + 1}"
    let actualIdent := actualIdents[originalIndex]!
    evalTactic (← `(tactic|
      generalize $equationIdent:ident : ($actualIdent:term) = $uIdent:ident))
    let uId ← getFVarId uIdent
    let equationId ← getFVarId equationIdent
    basisValues := basisValues.push (mkFVar uId)
    basisEquationIds := basisEquationIds.set! originalIndex (some equationId)

  -- Introduce every non-basis substitution equation.  Each proof is checked
  -- from the reduced constructor equality and the already introduced basis
  -- equations; the assignments returned by `isDefEq` only select the target.
  for i in [:actualValues.size] do
    if basisEquationIds[i]!.isNone then
      let rhs := replaceResiduals native.templates[i]!
        native.residuals basisValues
      let equationType ← (← getMainGoal).withContext do
        mkEq actualValues[i]! rhs
      let equationName := Name.mkSimple s!"h{i + 1}"
      discard <| assertBySimpAll equationName equationType

  -- Internal semantic witnesses are no longer part of the public interface.
  let goal ← getMainGoal
  let equalityId ← goal.withContext do
    let some decl := (← getLCtx).findFromUserName? equalityName
      | throwError "internal unification equality was lost"
    return decl.fvarId
  let stateId ← getFVarId stateIdent
  let goal ← goal.clear equalityId
  let goal ← goal.clear hpId
  let goal ← goal.clear hqId
  let goal ← goal.clear stateId
  setGoals [goal]


-- The examples intentionally come after the tactic implementation.

def pat1 (x1 x2 : Conf) : Conf := f x1 x2
def pat2 (y1 : Conf) : Conf := f (f y1 c) c

/- maude outputs the following unifier as a solution
variant unify in EX1 : f(X1, X2) =? f(f(Y1, c), c) .

Unifier 1
rewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)
X1 --> f(%1:Term, c)
X2 --> c
Y1 --> %1:Term

No more unifiers.
-/

#print pat1 -- λ x1 x2, f x1 x2
#print pat2 -- λ y1, f (f y1 c) c

-- pat1 ⋈ pat2 means pat1 & pat2 are unifiable
example (h : pat1 ⋈ pat2) : True := by
  unify h
  · exact True.intro


-- non-unifiable example
example (h : (fun x : Conf => f x x) ⋈ c) : False := by
  unify h


-- A differently named problem with two independent basis variables.  This is
-- below `unify`, so the tactic implementation cannot refer to either pattern.
def pairLeft (x1 x2 : Conf) : Conf := f x1 x2
def pairRight (y1 y2 : Conf) : Conf := f (f y1 y2) (f y2 y1)

-- X1 --> f(%1:Term, %2:Term)
-- X2 --> f(%2:Term, %1:Term)
-- Y1 --> %1:Term
-- Y2 --> %2:Term

#check pairLeft ⋈ pairRight -- : Prop

example (h : pairLeft ⋈ pairRight) : True := by
  unify h
  exact True.intro


-- Lambda closures work directly; named declarations are not required.
example
    (h : (fun a b : Conf => f a b) ⋈ (fun m : Conf => f m c)) : True := by
  unify h
  exact True.intro


-- A ground unification example
example (h : (f c c : Conf) ⋈ f c c) : True := by
  unify h
  exact True.intro












example (a b : Nat) : ∃ x y, x + y = a + b := by
  -- We introduce existential holes for x and y.
  -- Lean internally names these holes ?x and ?y (Metavariables).
  refine ⟨?x, ?y, ?eq⟩
  case eq =>
    exact rfl

end free_unification






namespace triangular_blowup
-- Triangular Blowup (or "Prolog's Nightmare")
-- P(x1, x2, x3, x4) = P(f(x2, x2), f(x3, x3), f(x4, x4), c)

inductive Term where
  | c : Term
  | f : Term → Term → Term
  deriving Repr

inductive Pred where
  | p : Term → Term → Term → Term → Pred
  deriving Repr

open Term Pred

def get_unified_x1 {x1 x2 x3 x4 : Term}
  (eq : p x1 x2 x3 x4 = p (f x2 x2) (f x3 x3) (f x4 x4) c) : Term :=
  x1

#eval get_unified_x1 rfl

-- this example only make sense when variables are shared

def pat1 (x1 x2 x3 x4 : Term) : Pred :=
  p x1 x2 x3 x4
#print pat1

def pat2 (x2 x3 x4 : Term) : Pred :=
  p (f x2 x2) (f x3 x3) (f x4 x4) c
#print pat2

-- what does unify pat1 pat2 mean? It means..
-- λ LHS.x1, LHS.x2, LHS.x3, LHS.x4, RHS.x2, RHS.x3, RHS.x4,
--   pat1 LHS.x1 LHS.x2 LHS.x3 LHS.x4 = pat2 RHS.x2 RHS.x3 RHS.x4
-- something like..
def unif_pat1_pat2 (x1 x2 x3 x4 y2 y3 y4: Term) : Prop :=
  p x1 x2 x3 x4 = p (f y2 y2) (f y3 y3) (f y4 y4) c

-- pat1 = pat2 doesn't make sense because e.g.
-- λ x1 x2, ⟨ x1, x2 ⟩ ≠ λ y, ⟨ 0, y ⟩
-- but we still want to unify them
-- (pat1 & pat2 do not share variables!)


/-- Same extraction function as before -/
def compute_unifiers (y2 y3 y4 : Term) {x1 x2 x3 x4 : Term}
  (eq : pat1 x1 x2 x3 x4 = pat2 y2 y3 y4) :
  Term × Term × Term × Term :=
  (x1, x2, x3, x4)

/--
  We wrap the computation in a new function that takes Lean's native
  variables (y2, y3, y4). By passing `rfl`, Lean's unifier silently
  computes the `x` variables in terms of the `y` variables.
-/
def unifier_function (y2 y3 y4 : Term) :=
  compute_unifiers y2 y3 y4 rfl

-- We use #reduce to inspect the evaluated body of the function.
#reduce unifier_function
end triangular_blowup
