import Lean


namespace framework

universe u v w x y

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

/-- The body returned by a constrained pattern closure. -/
structure PatternBody (α : Type u) where
  term : α
  requires : Prop := True

instance patternBodyAtPattern {α : Type u} [State α] :
    AtPattern α (PatternBody α) where
  semantics pattern state :=
    pattern.term = state ∧ pattern.requires

instance functionAtPattern {α : Type u} {A : Type v} {P : Type w}
    [State α] [AtPattern α P] : AtPattern α (A → P) where
  semantics p state := ∃ x, AtPattern.semantics (p x) state

/-- Patterns are atomic patterns closed under finite disjunction. -/
class Pattern (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

instance atomicPattern {α : Type u} {P : Type v}
    [State α] [AtPattern α P] :
    Pattern α P where
  semantics := AtPattern.semantics

/-- A heterogeneous disjunction of two pattern representations. -/
structure Disjunction (P : Type v) (Q : Type w) where
  left : P
  right : Q

infixr:65 " ⊔ " => framework.Disjunction.mk

instance disjunctionPattern {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q] :
    Pattern α (Disjunction P Q) where
  semantics patterns state :=
    Pattern.semantics patterns.left state ∨
    Pattern.semantics patterns.right state

/-- The empty pattern, used when narrowing returns no alternatives. -/
inductive EmptyPattern (α : Type u) where
  | empty : EmptyPattern α

instance emptyAtPattern {α : Type u} [State α] :
    AtPattern α (EmptyPattern α) where
  semantics _ _ := False

def Unifiable {α : Type u} {P : Type v} {Q : Type w}
    [State α] [AtPattern α P] [AtPattern α Q]
    (p : P) (q : Q) : Prop :=
  ∃ state, AtPattern.semantics p state ∧ AtPattern.semantics q state

infix:50 " ⋈ " => Unifiable

/-- The body returned by a constrained rewrite-rule closure. -/
structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  requires : Prop := True

-- Atomic rules and their Lean closures denote binary transition relations.
class AtRule (α : outParam (Type u)) [State α] (R : Type v) where
  semantics : R → α → α → Prop

instance ruleBodyAtRule {α : Type u} [State α] :
    AtRule α (RuleBody α) where
  semantics rule before after :=
    rule.lhs = before ∧ rule.rhs = after ∧ rule.requires

instance functionAtRule {α : Type u} {A : Type v} {R : Type w}
    [State α] [AtRule α R] : AtRule α (A → R) where
  semantics rule before after :=
    ∃ argument, AtRule.semantics (rule argument) before after

/-- The semantic one-step image of `source` under `rule`. -/
def postImage {α : Type u} {P : Type v} {R : Type w}
    [State α] [Pattern α P] [AtRule α R]
    (rule : R) (source : P) (after : α) : Prop :=
  ∃ before,
    Pattern.semantics source before ∧
    AtRule.semantics rule before after

/-- Semantic inclusion between two possibly different pattern representations. -/
def Subsumes {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q]
    (source : P) (target : Q) : Prop :=
  ∀ state, Pattern.semantics source state →
    Pattern.semantics target state

/-- A generated pattern is the exact one-step image of a rule and source. -/
def NarrowsTo {α : Type u} {P : Type v} {Post : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Post] [AtRule α R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after,
    Pattern.semantics post after ↔ postImage rule source after

/-- Every step of `rule` from a state denoted by `source` lands in `target`. -/
def mapsInto {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [AtRule α R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∀ before after,
    Pattern.semantics source before →
    AtRule.semantics rule before after →
    Pattern.semantics target after

notation:40 rule " ⊢ " source " ↝ " post =>
  NarrowsTo rule source post

notation:40 rule " ⊢ " source " ↪ " target =>
  mapsInto rule source target

infix:50 " ⊑ " => Subsumes

/-- Compose exact one-step narrowing with subsumption. -/
theorem mapsInto_of_narrowsTo_of_subsumes
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [Pattern α P] [Pattern α Post]
    [Pattern α Q] [AtRule α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hnarrow : NarrowsTo rule source post)
    (hsubsumes : Subsumes post target) :
    mapsInto rule source target := by
  intro before after hsource hrule
  apply hsubsumes after
  exact (hnarrow after).2 ⟨before, hsource, hrule⟩

/-- Once the exact post is known, `mapsInto` is precisely subsumption. -/
theorem mapsInto_iff_subsumes_of_narrowsTo
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [Pattern α P] [Pattern α Post]
    [Pattern α Q] [AtRule α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hnarrow : NarrowsTo rule source post) :
    mapsInto rule source target ↔ Subsumes post target := by
  constructor
  · intro hmaps state hpost
    obtain ⟨before, hsource, hrule⟩ := (hnarrow state).1 hpost
    exact hmaps before state hsource hrule
  · exact mapsInto_of_narrowsTo_of_subsumes hnarrow

end framework




namespace free_unification

open Lean Meta Elab Term Tactic
open framework

namespace Unification

/-!
The implementation is intentionally split into namespaces that can later
become files.  `Problem` knows how to read Lean pattern closures, `Certificate`
is the solver-neutral output format, `Free` is the native free-unification
backend, and `Presentation` controls the user-visible proof context.
-/

namespace Problem

/-- A pattern closure saturated with fresh, pairwise distinct metavariables. -/
structure SaturatedPattern where
  application : Expr
  arguments : Array Expr
  argumentNames : Array Name

/-- The first-order equation sent to a unification backend. -/
structure Input where
  lhs : SaturatedPattern
  rhs : SaturatedPattern

def visibleName (fallback : String) (name : Name) : Name :=
  if name.isAnonymous then Name.mkSimple fallback else name.eraseMacroScopes

/-- Saturate all explicit arguments of a pattern closure. -/
def saturatePattern (pattern : Expr) : MetaM SaturatedPattern := do
  let type ← inferType pattern
  let (arguments, binderInfos, _) ← forallMetaTelescopeReducing type
  unless binderInfos.all fun info => info == .default do
    throwError "`unify` only supports explicit pattern arguments"
  let mut argumentNames := #[]
  for argument in arguments do
    let decl ← argument.mvarId!.getDecl
    argumentNames := argumentNames.push decl.userName.eraseMacroScopes
  return {
    application := mkAppN pattern arguments
    arguments
    argumentNames
  }

/-- Extract the two patterns from a proposition `p ⋈ q`. -/
def ofUnifiableType (type : Expr) : MetaM Input := do
  let type ← instantiateMVars type
  let arguments := type.getAppArgs
  unless type.getAppFn.isConstOf ``Unifiable && arguments.size >= 2 do
    throwError "expected a hypothesis of the form `p ⋈ q`"
  let lhs ← saturatePattern arguments[arguments.size - 2]!
  let rhs ← saturatePattern arguments[arguments.size - 1]!
  return { lhs, rhs }

def argumentCount (problem : Input) : Nat :=
  problem.lhs.arguments.size + problem.rhs.arguments.size

def symbolicArguments (problem : Input) : Array Expr :=
  problem.lhs.arguments ++ problem.rhs.arguments

end Problem


namespace Certificate

/--
A solver-neutral unifier branch.

Each `image` is a lambda over all `basisTypes`.  Consequently this structure
contains no metavariables owned by a particular backend.  An AC backend can
return several values of this type; the free backend returns at most one.
-/
structure Alternative where
  basisTypes : Array Expr
  images : Array Expr
  deriving Inhabited

/-- A branch together with a kernel-checked proof of its factorization. -/
structure ProvenAlternative where
  alternative : Alternative
  proposition : Expr
  proof : Expr

/-- The common result shape for unitary and multi-unifier backends. -/
structure SolutionSet where
  alternatives : Array Alternative

/-- A complete, checked disjunction of all alternatives returned by a backend. -/
structure ProvenSolutionSet where
  solutionSet : SolutionSet
  branchPropositions : Array Expr
  proposition : Expr
  proof : Expr

private def mkAndAll (propositions : Array Expr) : MetaM Expr := do
  let mut result := Lean.mkConst ``True
  for proposition in propositions.toList.reverse do
    result ← mkAppM ``And #[proposition, result]
  return result

private def mkExistsOne (variableExpr body : Expr) : MetaM Expr := do
  let predicate ← mkLambdaFVars #[variableExpr] body
  mkAppM ``Exists #[predicate]

private def mkExistsOver (variables : Array Expr) (body : Expr) : MetaM Expr := do
  let mut result := body
  for variableExpr in variables.toList.reverse do
    result ← mkExistsOne variableExpr result
  return result

private def mkOrAll (propositions : Array Expr) : MetaM Expr := do
  if propositions.isEmpty then
    return Lean.mkConst ``False
  let mut result := propositions[propositions.size - 1]!
  for proposition in propositions.toList.dropLast.reverse do
    result ← mkAppM ``Or #[proposition, result]
  return result

private partial def withBasisVariables
    {α : Type}
    (types : Array Expr) (index : Nat) (variables : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun variableExpr =>
        withBasisVariables types (index + 1) (variables.push variableExpr)
          continuation
  else
    continuation variables

/-- Instantiate one substitution image at concrete basis values. -/
def instantiateImage (image : Expr) (basis : Array Expr) : Expr :=
  mkAppN image basis

/--
Turn a branch into its public logical meaning:

`∃ u₁ ... uₖ, x₁ = image₁ u ∧ ... ∧ xₙ = imageₙ u ∧ True`.
-/
def factorizationType
    (alternative : Alternative) (actualArguments : Array Expr) : MetaM Expr := do
  unless alternative.images.size == actualArguments.size do
    throwError "a unification branch has the wrong number of substitution images"
  withBasisVariables alternative.basisTypes 0 #[] fun basis => do
    let mut equations := #[]
    for i in [:actualArguments.size] do
      let image ← whnf (instantiateImage alternative.images[i]! basis)
      equations := equations.push (← mkEq actualArguments[i]! image)
    let body ← mkAndAll equations
    mkExistsOver basis body

/-- Build the disjunction represented by an entire solver result. -/
def solutionSetType
    (solutionSet : SolutionSet) (actualArguments : Array Expr) : MetaM
      (Array Expr × Expr) := do
  let mut branches := #[]
  for alternative in solutionSet.alternatives do
    branches := branches.push (← factorizationType alternative actualArguments)
  return (branches, ← mkOrAll branches)

end Certificate


namespace Free

/-- Extra evidence used only while certifying a native free-unification result. -/
structure Candidate where
  alternative : Certificate.Alternative
  /-- For the free theory, every residual basis value is an original argument. -/
  basisWitnesses : Array Nat
  deriving Inhabited

structure Output where
  candidates : Array Candidate := #[]

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

private partial def withBasisVariables
    {α : Type}
    (types : Array Expr) (index : Nat) (variables : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun variableExpr =>
        withBasisVariables types (index + 1) (variables.push variableExpr)
          continuation
  else
    continuation variables

/--
Compute the unique MGU for a free first-order problem with Lean's native
unifier.  Residual native metavariables are abstracted immediately into lambda
bound basis variables; they never cross this backend boundary.
-/
def solve (problem : Problem.Input) : MetaM Output := do
  unless ← isDefEq problem.lhs.application problem.rhs.application do
    return {}

  let symbolicArguments := Problem.symbolicArguments problem
  let mut templates := #[]
  let mut residuals := #[]
  for argument in symbolicArguments do
    let template ← instantiateMVars argument
    templates := templates.push template
    for residual in ← getMVars template do
      unless residuals.contains residual do
        residuals := residuals.push residual

  let mut basisTypes := #[]
  let mut basisWitnesses := #[]
  for residual in residuals do
    let some originalIndex := symbolicArguments.findIdx? fun argument =>
        argument.isMVar && argument.mvarId! == residual
      | throwError "native unification introduced an unexpected metavariable"
    let type ← instantiateMVars (← residual.getType)
    unless (← getMVars type).isEmpty do
      throwError "dependent basis types are outside the supported free fragment"
    basisTypes := basisTypes.push type
    basisWitnesses := basisWitnesses.push originalIndex

  let images ← withBasisVariables basisTypes 0 #[] fun basis => do
    let mut images := #[]
    for template in templates do
      let body := replaceResiduals template residuals basis
      unless (← getMVars body).isEmpty do
        throwError "native unification left an unabstracted metavariable"
      images := images.push (← mkLambdaFVars basis body)
    return images

  return { candidates := #[{
      alternative := { basisTypes, images }
      basisWitnesses
    }] }

/--
Prove the factorization selected by `solve`.  The native assignment chooses
the proposition, but `simp_all` must prove it from the constructor equality;
therefore `isDefEq` is not trusted as a proof-producing oracle.
-/
def certifySuccess
    (solution : Candidate) (actualArguments : Array Expr)
    (actualIdents : Array Ident) (irrelevant : Array FVarId := #[]) : TacticM
      Certificate.ProvenAlternative := do
  let goal ← getMainGoal
  let proposition ← goal.withContext do
    Certificate.factorizationType solution.alternative actualArguments
  let proof ← goal.withContext do mkFreshExprMVar (some proposition)
  let mut certificationGoal := proof.mvarId!
  for hypothesis in irrelevant do
    certificationGoal ← certificationGoal.clear hypothesis
  replaceMainGoal [certificationGoal]
  for witnessIndex in solution.basisWitnesses do
    let witnessIdent := actualIdents[witnessIndex]!
    evalTactic (← `(tactic| refine Exists.intro $witnessIdent ?_))
  evalTactic (← `(tactic| simp_all))
  unless ← proof.mvarId!.isAssigned do
    throwError "failed to certify the native free-unification result"
  setGoals [goal]
  return { alternative := solution.alternative, proposition, proof }

private partial def collectEqualityLeaves
    (proof : Expr) (result : Array Expr := #[]) : MetaM (Array Expr) := do
  let type ← whnf (← inferType proof)
  if type.eq?.isSome then
    return result.push proof
  let arguments := type.getAppArgs
  if type.getAppFn.isConstOf ``And && arguments.size == 2 then
    let left ← mkAppM ``And.left #[proof]
    let right ← mkAppM ``And.right #[proof]
    let result ← collectEqualityLeaves left result
    collectEqualityLeaves right result
  else
    return result

private def noteSizeEquation (goal : MVarId) (equality : Expr) : MetaM MVarId :=
    goal.withContext do
  let equalityType ← whnf (← inferType equality)
  let some (type, _, _) := equalityType.eq?
    | return goal
  try
    let sizeFunction ← withLocalDeclD `_unifySizeArgument type fun argument => do
      let size ← mkAppM ``SizeOf.sizeOf #[argument]
      mkLambdaFVars #[argument] size
    let sizeEquality ← mkAppM ``congrArg #[sizeFunction, equality]
    let sizeEqualityType ← inferType sizeEquality
    let name := (← getLCtx).getUnusedName `_unifySizeEq
    let (_, goal) ← goal.note name sizeEquality (some sizeEqualityType)
    return goal
  catch _ =>
    -- Constructor clashes do not need `SizeOf`.  An occurs-check cycle does;
    -- if its state type has no `SizeOf` instance, the final certification step
    -- reports that this input is outside the currently supported fragment.
    return goal

/--
Certify failure returned by the native free backend.  `simp_all` proves direct
constructor clashes.  For occurs-check cycles, every constructor equation is
also mapped through `sizeOf`; generated inductive `SizeOf` equations reduce to
inconsistent natural-number constraints, which `omega` checks.
-/
private def certifyFailureGoal : TacticM Unit := do
  evalTactic (← `(tactic| simp_all))
  if (← getGoals).isEmpty then
    return

  let mut goal ← getMainGoal
  let equalityProofs ← goal.withContext do
    let mut equalityProofs := #[]
    for declaration in ← getLCtx do
      if declaration.isImplementationDetail then
        continue
      equalityProofs ← collectEqualityLeaves (mkFVar declaration.fvarId)
        equalityProofs
    return equalityProofs
  for equality in equalityProofs do
    goal ← noteSizeEquation goal equality
  setGoals [goal]

  try
    evalTactic (← `(tactic| solve | (simp_all <;> omega)))
  catch _ =>
    throwError
      "free unification found no solution, but could not certify the contradiction"

private def certifyFailure (irrelevant : Array FVarId) : TacticM Expr := do
  let goal ← getMainGoal
  let falseProof ← goal.withContext do
    mkFreshExprMVar (some (Lean.mkConst ``False))
  let mut certificationGoal := falseProof.mvarId!
  for hypothesis in irrelevant do
    certificationGoal ← certificationGoal.clear hypothesis
  replaceMainGoal [certificationGoal]
  certifyFailureGoal
  unless ← falseProof.mvarId!.isAssigned do
    throwError "failed to construct the free-unification refutation"
  setGoals [goal]
  return falseProof

/--
Turn the free backend's private evidence into the common, complete result
certificate consumed by `Presentation`.
-/
def certify
    (output : Output) (actualArguments : Array Expr)
    (actualIdents : Array Ident) (irrelevant : Array FVarId := #[]) :
    TacticM Certificate.ProvenSolutionSet := do
  let solutionSet : Certificate.SolutionSet := {
    alternatives := output.candidates.map (·.alternative)
  }
  match output.candidates.size with
  | 0 =>
      let proof ← certifyFailure irrelevant
      return {
        solutionSet
        branchPropositions := #[]
        proposition := Lean.mkConst ``False
        proof
      }
  | 1 =>
      let proven ← certifySuccess output.candidates[0]!
        actualArguments actualIdents irrelevant
      return {
        solutionSet
        branchPropositions := #[proven.proposition]
        proposition := proven.proposition
        proof := proven.proof
      }
  | _ =>
      throwError "the free backend unexpectedly returned more than one MGU"

end Free


namespace Presentation

def freshVisibleIdent (ref : Syntax) (base : Name) : TacticM Ident := do
  let goal ← getMainGoal
  let name ← goal.withContext do
    return (← getLCtx).getUnusedName base
  return mkIdentFrom ref name

private def singleCases (goal : MVarId) (hypothesis : FVarId) : MetaM
    (MVarId × Array FVarId) := do
  let subgoals ← goal.cases hypothesis
  let [subgoal] := subgoals.toList
    | throwError "unexpected branching while exposing a unifier certificate"
  let fields := subgoal.fields.filterMap fun
    | .fvar id => some id
    | _ => none
  return (subgoal.mvarId, fields)

/-- Open one proven branch on a specified goal. -/
private def exposeAlternativeAt
    (goal : MVarId) (proven : Certificate.ProvenAlternative) : MetaM MVarId := do
  let factorizationName ← goal.withContext do
    return (← getLCtx).getUnusedName `_unifyFactorization
  let (factorizationId, goal) ← goal.withContext do
    goal.note factorizationName proven.proof (some proven.proposition)

  let mut goal := goal
  let mut bodyId := factorizationId
  for i in [:proven.alternative.basisTypes.size] do
    let (nextGoal, fields) ← goal.withContext do singleCases goal bodyId
    unless fields.size >= 2 do
      throwError "malformed existential unifier certificate"
    let basisName ← nextGoal.withContext do
      return (← getLCtx).getUnusedName (Name.mkSimple s!"u{i + 1}")
    goal ← nextGoal.rename fields[0]! basisName
    bodyId := fields[fields.size - 1]!

  for i in [:proven.alternative.images.size] do
    let (nextGoal, fields) ← goal.withContext do singleCases goal bodyId
    unless fields.size >= 2 do
      throwError "malformed conjunction in unifier certificate"
    let equationName ← nextGoal.withContext do
      return (← getLCtx).getUnusedName (Name.mkSimple s!"h{i + 1}")
    goal ← nextGoal.rename fields[0]! equationName
    bodyId := fields[fields.size - 1]!

  -- The conjunction has a final `True`, used to make the zero-argument case
  -- uniform.  It is an implementation detail and is removed here.
  goal ← goal.clear bodyId
  return goal

private partial def exposeAlternativesAt
    (goal : MVarId) (hypothesis : FVarId)
    (proven : Certificate.ProvenSolutionSet) (index : Nat) : MetaM (List MVarId) := do
  let remaining := proven.solutionSet.alternatives.size - index
  if remaining == 1 then
    let goal ← exposeAlternativeAt goal {
      alternative := proven.solutionSet.alternatives[index]!
      proposition := proven.branchPropositions[index]!
      proof := mkFVar hypothesis
    }
    return [goal]

  let subgoals ← goal.cases hypothesis
  let [left, right] := subgoals.toList
    | throwError "malformed disjunction in unification result certificate"
  let some leftProof := left.fields.back?
    | throwError "failed to expose a unifier branch"
  let some rightProof := right.fields.back?
    | throwError "failed to expose the remaining unifier branches"
  let .fvar leftProof := leftProof
    | throwError "failed to expose a unifier branch"
  let .fvar rightProof := rightProof
    | throwError "failed to expose the remaining unifier branches"
  let leftGoal ← exposeAlternativeAt left.mvarId {
    alternative := proven.solutionSet.alternatives[index]!
    proposition := proven.branchPropositions[index]!
    proof := mkFVar leftProof
  }
  let rightGoals ← exposeAlternativesAt right.mvarId rightProof proven (index + 1)
  return leftGoal :: rightGoals

/--
Open a complete solver result into the stable public interface.  One branch
creates one goal; several alternatives create several goals.  Every goal has
basis variables `u1`, `u2`, ... followed by equations `h1`, `h2`, ... in
original-argument order.  An empty result closes the goal by contradiction.
-/
def expose (proven : Certificate.ProvenSolutionSet) : TacticM Unit := do
  let goal ← getMainGoal
  match proven.solutionSet.alternatives.size with
  | 0 =>
      let falseName ← goal.withContext do
        return (← getLCtx).getUnusedName `_unifyImpossible
      let (_, goal) ← goal.withContext do
        goal.note falseName proven.proof (some proven.proposition)
      setGoals [goal]
      evalTactic (← `(tactic| contradiction))
  | 1 =>
      let goal ← exposeAlternativeAt goal {
        alternative := proven.solutionSet.alternatives[0]!
        proposition := proven.branchPropositions[0]!
        proof := proven.proof
      }
      setGoals [goal]
  | _ =>
      let disjunctionName ← goal.withContext do
        return (← getLCtx).getUnusedName `_unifyAlternatives
      let (disjunctionId, goal) ← goal.withContext do
        goal.note disjunctionName proven.proof (some proven.proposition)
      let goals ← goal.withContext do
        exposeAlternativesAt goal disjunctionId proven 0
      setGoals goals

end Presentation


namespace Tactic

private structure SemanticWitnesses where
  actualArguments : Array Expr
  actualIdents : Array Ident
  stateId : FVarId
  lhsSemanticsId : FVarId
  rhsSemanticsId : FVarId
  equalityId : FVarId

private def exposeSemantics
    (ref : Syntax) (h : Ident) (problem : Problem.Input) : TacticM
      SemanticWitnesses := do
  let stateIdent ← Presentation.freshVisibleIdent ref `_unifyState
  let lhsIdent ← Presentation.freshVisibleIdent ref `_unifyLhs
  let rhsIdent ← Presentation.freshVisibleIdent ref `_unifyRhs
  evalTactic (← `(tactic|
    rcases ($h:term) with
      ⟨$stateIdent:ident, $lhsIdent:ident, $rhsIdent:ident⟩))

  let mut actualIdents := #[]
  for i in [:problem.lhs.arguments.size] do
    let base := Problem.visibleName s!"x{i + 1}"
      problem.lhs.argumentNames[i]!
    let argumentIdent ← Presentation.freshVisibleIdent ref base
    evalTactic (← `(tactic|
      rcases ($lhsIdent:term) with ⟨$argumentIdent:ident, $lhsIdent:ident⟩))
    actualIdents := actualIdents.push argumentIdent
  for i in [:problem.rhs.arguments.size] do
    let base := Problem.visibleName s!"y{i + 1}"
      problem.rhs.argumentNames[i]!
    let argumentIdent ← Presentation.freshVisibleIdent ref base
    evalTactic (← `(tactic|
      rcases ($rhsIdent:term) with ⟨$argumentIdent:ident, $rhsIdent:ident⟩))
    actualIdents := actualIdents.push argumentIdent

  let actualIds ← actualIdents.mapM getFVarId
  let actualArguments := actualIds.map mkFVar
  let lhsSemanticsId ← getFVarId lhsIdent
  let rhsSemanticsId ← getFVarId rhsIdent

  -- Compose both equalities with the shared semantic state, then unfold the
  -- pattern bodies.  This equality is the kernel-checked input to certification.
  let goal ← getMainGoal
  let equalityName ← goal.withContext do
    return (← getLCtx).getUnusedName `_unifyEq
  let (equalityType, equalityProof) ← goal.withContext do
    let rhsSymm ← mkAppM ``Eq.symm #[mkFVar rhsSemanticsId]
    let proof ← mkAppM ``Eq.trans #[mkFVar lhsSemanticsId, rhsSymm]
    let proofType ← whnf (← inferType proof)
    let some (_, lhs, rhs) := proofType.eq?
      | throwError "malformed atomic-pattern semantics"
    let lhs ← withTransparency .all <| whnf lhs
    let rhs ← withTransparency .all <| whnf rhs
    return (← mkEq lhs rhs, proof)
  let (equalityId, goal) ← goal.withContext do
    goal.note equalityName equalityProof (some equalityType)
  setGoals [goal]

  return {
    actualArguments
    actualIdents
    stateId := ← getFVarId stateIdent
    lhsSemanticsId
    rhsSemanticsId
    equalityId
  }

private def clearSemantics (witnesses : SemanticWitnesses) : TacticM Unit := do
  let mut clearedGoals := #[]
  for goal in ← getGoals do
    let goal ← goal.clear witnesses.equalityId
    let goal ← goal.clear witnesses.lhsSemanticsId
    let goal ← goal.clear witnesses.rhsSemanticsId
    let goal ← goal.clear witnesses.stateId
    clearedGoals := clearedGoals.push goal
  setGoals clearedGoals.toList

/-- Run the native free-unification backend and expose its certified MGU. -/
def run (ref : Syntax) (h : Ident) : TacticM Unit := do
  let hypothesisId ← getFVarId h
  let hypothesisType ← instantiateMVars (← hypothesisId.getType)
  let initialGoal ← getMainGoal
  let (problem, output) ← initialGoal.withContext do
    let problem ← Problem.ofUnifiableType hypothesisType
    let output ← Free.solve problem
    return (problem, output)

  let witnesses ← exposeSemantics ref h problem
  let proven ← try
      Free.certify output witnesses.actualArguments witnesses.actualIdents
        #[witnesses.lhsSemanticsId, witnesses.rhsSemanticsId, witnesses.stateId]
    catch exception =>
      throwErrorAt h exception.toMessageData
  Presentation.expose proven
  clearSemantics witnesses

end Tactic

end Unification

/--
Compute and certify the MGU of the free first-order unification problem in `h`.
On success it introduces basis variables `u1`, `u2`, ... and one equation per
original pattern argument.  On failure it closes the goal by contradiction.
-/
elab "unify " h:ident : tactic =>
  Unification.Tactic.run h.raw h


namespace Narrowing

/-!
`Narrowing` is an adapter around the generic unification API.  It extracts the
structural equation between a rule LHS and a source-pattern term, delegates
that equation to a backend, and reconnects the certified substitutions to the
rule RHS and both constraints.
-/

namespace Problem

/-- A rule closure whose binders were saturated together exactly once. -/
structure SaturatedRule where
  value : Expr
  closure : Unification.Problem.SaturatedPattern
  lhs : Expr
  rhs : Expr
  requires : Expr

/-- A constrained pattern closure saturated exactly once. -/
structure SaturatedConstrainedPattern where
  value : Expr
  closure : Unification.Problem.SaturatedPattern
  term : Expr
  requires : Expr

/-- Everything needed for one structural narrowing problem. -/
structure Input where
  rule : SaturatedRule
  source : SaturatedConstrainedPattern
  unification : Unification.Problem.Input

private def project (projection : Name) (value : Expr) : MetaM Expr := do
  withTransparency .all <| whnf (← mkAppM projection #[value])

def saturateRule (rule : Expr) : MetaM SaturatedRule := do
  let closure ← Unification.Problem.saturatePattern rule
  let application ← withTransparency .all <| whnf closure.application
  try
    return {
      value := rule
      closure
      lhs := ← project ``RuleBody.lhs application
      rhs := ← project ``RuleBody.rhs application
      requires := ← project ``RuleBody.requires application
    }
  catch _ =>
    throwError "`narrow` expects a closure returning `RuleBody`"

def saturateSource (source : Expr) : MetaM SaturatedConstrainedPattern := do
  let closure ← Unification.Problem.saturatePattern source
  let application ← withTransparency .all <| whnf closure.application
  try
    return {
      value := source
      closure
      term := ← project ``PatternBody.term application
      requires := ← project ``PatternBody.requires application
    }
  catch _ =>
    throwError "`narrow` expects a closure returning `PatternBody`"

/-- Form the backend problem `rule.lhs = source.term`. -/
def ofTerms (rule source : Expr) : MetaM Input := do
  let rule ← saturateRule rule
  let source ← saturateSource source
  let lhs : Unification.Problem.SaturatedPattern := {
    rule.closure with application := rule.lhs
  }
  let rhs : Unification.Problem.SaturatedPattern := {
    source.closure with application := source.term
  }
  return { rule, source, unification := { lhs, rhs } }

def symbolicArguments (problem : Input) : Array Expr :=
  Unification.Problem.symbolicArguments problem.unification

end Problem


namespace Goal

/-- The three user objects encoded in a `mapsInto` target. -/
structure Input where
  rule : Expr
  source : Expr
  target : Expr

def ofMapsIntoType (type : Expr) : MetaM Input := do
  let type ← instantiateMVars type
  let arguments := type.getAppArgs
  unless type.getAppFn.isConstOf ``mapsInto && arguments.size >= 3 do
    throwError "`narrow` expects a goal of the form `mapsInto rule source target`"
  return {
    rule := arguments[arguments.size - 3]!
    source := arguments[arguments.size - 2]!
    target := arguments[arguments.size - 1]!
  }

end Goal


namespace Backend

/--
The current backend bridge.  Backend-private evidence is erased here; all
later narrowing phases consume only the common solver-neutral solution set.
-/
def solve (problem : Problem.Input) : MetaM Unification.Certificate.SolutionSet := do
  let output ← Unification.Free.solve problem.unification
  return { alternatives := output.candidates.map (·.alternative) }

end Backend


namespace Materialization

/-- A generated post together with its concrete (possibly heterogeneous) type. -/
structure Post where
  type : Expr
  value : Expr

private partial def withBasisVariables
    {α : Type}
    (types : Array Expr) (index : Nat) (variables : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun basisVariable =>
        withBasisVariables types (index + 1) (variables.push basisVariable)
          continuation
  else
    continuation variables

private def projections (problem : Problem.Input)
    (alternative : Unification.Certificate.Alternative)
    (basis : Array Expr) : MetaM (Expr × Expr × Expr) := do
  let mut images := #[]
  for image in alternative.images do
    images := images.push (← whnf
      (Unification.Certificate.instantiateImage image basis))
  let ruleCount := problem.rule.closure.arguments.size
  let sourceCount := problem.source.closure.arguments.size
  unless images.size == ruleCount + sourceCount do
    throwError "a narrowing alternative has the wrong number of images"
  let ruleArguments := images.extract 0 ruleCount
  let sourceArguments := images.extract ruleCount images.size
  let ruleValue ← withTransparency .all <|
    whnf (mkAppN problem.rule.value ruleArguments)
  let sourceValue ← withTransparency .all <|
    whnf (mkAppN problem.source.value sourceArguments)
  let rhs ← withTransparency .all <|
    whnf (← mkAppM ``RuleBody.rhs #[ruleValue])
  let ruleRequires ← withTransparency .all <|
    whnf (← mkAppM ``RuleBody.requires #[ruleValue])
  let sourceRequires ← withTransparency .all <|
    whnf (← mkAppM ``PatternBody.requires #[sourceValue])
  return (rhs, sourceRequires, ruleRequires)

/-- Turn one backend alternative into its constrained successor closure. -/
def successor (problem : Problem.Input)
    (alternative : Unification.Certificate.Alternative) : MetaM Expr := do
  withBasisVariables alternative.basisTypes 0 #[] fun basis => do
    let (rhs, sourceRequires, ruleRequires) ←
      projections problem alternative basis
    let requires ← mkAppM ``And #[sourceRequires, ruleRequires]
    let body ← mkAppM ``PatternBody.mk #[rhs, requires]
    mkLambdaFVars basis body

private def empty (problem : Problem.Input) : MetaM Expr := do
  let stateType ← inferType problem.rule.lhs
  let .sort (.succ level) ← whnf (← inferType stateType)
    | throwError "the narrowing state is not a type"
  return mkApp (mkConst ``EmptyPattern.empty [level]) stateType

private def disjoin (left right : Expr) : MetaM Expr :=
  mkAppM ``Disjunction.mk #[left, right]

/--
Materialize every MGU as an atomic successor and combine the successors into
the complete `Pattern` post.  The free backend yields zero or one successor;
the fold already supports a future multi-unifier backend.
-/
def post (problem : Problem.Input)
    (alternatives : Array Unification.Certificate.Alternative) : MetaM Post := do
  let value ← if alternatives.isEmpty then
      empty problem
    else
      let mut value ← successor problem alternatives[alternatives.size - 1]!
      for alternative in alternatives.toList.dropLast.reverse do
        value ← disjoin (← successor problem alternative) value
      pure value
  return { type := ← inferType value, value }

end Materialization


namespace Certification

/--
Find the definition, if any, that directly supplies a rule or pattern closure.
For example, both `advance` and `fun x y => advance x y` select `advance`.
Record constructors and fully inline closures need no extra unfolding lemma.
-/
private partial def closureDefinition? (expression : Expr) : Option Name :=
  match expression.consumeMData with
  | .lam _ _ body _ => closureDefinition? body
  | .letE _ _ _ body _ => closureDefinition? body
  | expression =>
      match expression.getAppFn with
      | .const name _ => some name
      | _ => none

private def unfoldingDefinitions
    (goalInput : Goal.Input) : CoreM (Array Name) := do
  let environment ← getEnv
  let mut result := #[]
  for expression in #[goalInput.rule, goalInput.source] do
    let some name := closureDefinition? expression | continue
    let isDefinition := match environment.find? name with
      | some (.defnInfo _) | some (.opaqueInfo _) => true
      | _ => false
    if isDefinition && !result.contains name then
      result := result.push name
  return result

/--
Certify that the materialized post is the complete one-step image.  This
prototype replays free constructor reasoning with `simp` and `grind`; an AC
backend can replace this namespace with certificate replay for its theory.
-/
def prove (ref : Syntax) (goalInput : Goal.Input)
    (ruleSyntax sourceSyntax : TSyntax `term) (postIdent : Ident) :
    TacticM Ident := do
  let narrowingIdent ←
    Unification.Presentation.freshVisibleIdent ref `narrowing
  let unfoldNames ← unfoldingDefinitions goalInput
  let unfoldSimps ← unfoldNames.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
  try
    evalTactic (← `(tactic|
      have $narrowingIdent:ident :
          NarrowsTo $ruleSyntax $sourceSyntax ($postIdent:term) := by
        simp [NarrowsTo, postImage, Pattern.semantics,
          AtPattern.semantics, AtRule.semantics,
          $postIdent:term, $unfoldSimps,*] <;>
          grind))
  catch exception =>
    throwErrorAt ref m!"failed to certify the generated narrowing post:\n{exception.toMessageData}"
  return narrowingIdent

end Certification


namespace Tactic

private def checkUserTerms
    (goalInput : Goal.Input) (ruleSyntax sourceSyntax : Syntax) : TacticM Unit := do
  let rule ← Tactic.elabTerm ruleSyntax (some (← inferType goalInput.rule))
  let source ← Tactic.elabTerm sourceSyntax (some (← inferType goalInput.source))
  unless ← isDefEq rule goalInput.rule do
    throwErrorAt ruleSyntax "this is not the rule in the `mapsInto` goal"
  unless ← isDefEq source goalInput.source do
    throwErrorAt sourceSyntax "this is not the source pattern in the `mapsInto` goal"

private def bindPost (ref : Syntax) (post : Materialization.Post) :
    TacticM Ident := do
  let goal ← getMainGoal
  let name ← goal.withContext do
    return (← getLCtx).getUnusedName `post
  let goal ← goal.define name post.type post.value
  let (_, goal) ← goal.intro1P
  setGoals [goal]
  return mkIdentFrom ref name

/--
Generate and bind the exact one-step post, prove its narrowing judgment, and
reduce a `mapsInto` goal to subsumption of that generated post.
-/
def run (ref : Syntax) (ruleSyntax sourceSyntax : TSyntax `term) : TacticM Unit := do
  let initialGoal ← getMainGoal
  let (goalInput, generatedPost) ← initialGoal.withContext do
    let goalInput ← Goal.ofMapsIntoType (← initialGoal.getType)
    checkUserTerms goalInput ruleSyntax.raw sourceSyntax.raw
    let problem ← Problem.ofTerms goalInput.rule goalInput.source
    let solutionSet ← Backend.solve problem
    let generatedPost ← Materialization.post problem solutionSet.alternatives
    return (goalInput, generatedPost)

  let postIdent ← bindPost ref generatedPost
  let narrowingIdent ← Certification.prove ref goalInput
    ruleSyntax sourceSyntax postIdent

  evalTactic (← `(tactic|
    apply mapsInto_of_narrowsTo_of_subsumes
      ($narrowingIdent:term)))

end Tactic

end Narrowing

/-- Perform one constrained narrowing step for a single rule and source. -/
elab "narrow " rule:term " against " source:term : tactic =>
  Narrowing.Tactic.run rule.raw rule source

end free_unification








namespace examples

open framework
open free_unification

-- User-defined model for the examples.  It is deliberately not part of the
-- generic free-unification implementation, and it needs no `var` constructor.
inductive Conf where
  | c : Conf
  | f : Conf → Conf → Conf
  deriving Repr

instance : State Conf := ⟨⟩

open Conf

-- The examples intentionally live outside the implementation namespace and
-- come after the tactic implementation.

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
  guard_hyp u1 : Conf
  guard_hyp h1 : x1 = f u1 c
  guard_hyp h2 : x2 = c
  guard_hyp h3 : y1 = u1
  exact True.intro


-- non-unifiable example
example (h : (fun x : Conf => f x x) ⋈ c) : False := by
  unify h

-- Failure produces a proof of `False`, so it closes an arbitrary target rather
-- than relying on the target itself being syntactically `False`.
example (h : (c : Conf) ⋈ f c c) : (0 : Nat) = 1 := by
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
  guard_hyp u1 : Conf
  guard_hyp u2 : Conf
  guard_hyp h1 : x1 = f u1 u2
  guard_hyp h2 : x2 = f u2 u1
  guard_hyp h3 : y1 = u1
  guard_hyp h4 : y2 = u2
  exact True.intro


-- Lambda closures work directly; named declarations are not required.
example
    (h : (fun a b : Conf => f a b) ⋈ (fun m : Conf => f m c)) : True := by
  unify h
  guard_hyp u1 : Conf
  guard_hyp h1 : a = u1
  guard_hyp h2 : b = c
  guard_hyp h3 : m = u1
  exact True.intro


-- Pure variables still produce a basis rather than an object-language `var`.
example (h : (fun left : Conf => left) ⋈ (fun right : Conf => right)) : True := by
  unify h
  guard_hyp u1 : Conf
  guard_hyp h1 : left = u1
  guard_hyp h2 : right = u1
  exact True.intro


-- A deeper cascading substitution exercises native unification and certificate
-- reconstruction independently of any declaration names.
example
    (h : (fun a b d : Conf => f a (f b d)) ⋈
      (fun x : Conf => f (f x c) (f c x))) : True := by
  unify h
  guard_hyp u1 : Conf
  guard_hyp h1 : a = f u1 c
  guard_hyp h2 : b = c
  guard_hyp h3 : d = u1
  guard_hyp h4 : x = u1
  exact True.intro


-- A ground unification example
example (h : (f c c : Conf) ⋈ f c c) : True := by
  unify h
  exact True.intro


-- An occurs-check failure: the constructor equations would imply
-- `y = f y c`, which no finite `Conf` can satisfy.
example
    (h : (fun x : Conf => f x x) ⋈
      (fun y : Conf => f (f y c) y)) : False := by
  unify h


end examples


namespace narrowing_examples

open framework
open free_unification

/-!
This model, its patterns, and its rules are user code.  In particular, the
model has no constructor for logical variables.
-/
inductive Conf where
  | atom : Nat → Conf
  | pair : Conf → Conf → Conf
  deriving Repr

instance : State Conf := ⟨⟩

open Conf

/-- `pair (atom 0) (atom n) where n > 0` -/
def source (n : Nat) : PatternBody Conf where
  term := pair (atom 0) (atom n)
  requires := 0 < n

/-- `pair (atom payload) (atom (payload + 1))` where `payload > 0` -/
def target (payload : Nat) : PatternBody Conf where
  term := pair (atom payload) (atom (payload + 1))
  requires := 0 < payload

/-  rl : pair (atom 0) (atom payload)
 => pair (atom payload) (atom next)
 if next = payload + 1` -/
def advance (payload next : Nat) : RuleBody Conf where
  lhs := pair (atom 0) (atom payload)
  rhs := pair (atom payload) (atom next)
  requires := next = payload + 1

example : advance ⊢ source ↪ target := by
  narrow advance against source
  -- `post` is generated by the tactic; the user supplies no intermediate
  -- pattern.  Only the subsumption phase remains.
  simp [Subsumes, Pattern.semantics, AtPattern.semantics, post, target]
  grind

/-- A rule whose constructor-headed LHS cannot match `source`. -/
def blocked : RuleBody Conf where
  lhs := pair (atom 1) (atom 0)
  rhs := atom 0

-- With no structural unifier, the assumed step is impossible and `narrow`
-- closes the `mapsInto` proof.  No special lemma about `blocked` is supplied.
example : blocked ⊢ source ↪ target := by
  narrow blocked against source
  simp [Subsumes, Pattern.semantics, AtPattern.semantics]

/- This LHS matches `source`, but its constraint requires the matched positive
payload to be zero. -/
def constrainedOut (payload : Nat) : RuleBody Conf where
  lhs := pair (atom 0) (atom payload)
  rhs := atom payload
  requires := payload = 0

-- Structural unification returns an MGU branch.  Its instantiated constraints
-- are `0 < n` and `payload = 0`, so the constraints filter that branch out.
example : constrainedOut ⊢ source ↪ target := by
  narrow constrainedOut against source
  simp [Subsumes, Pattern.semantics, AtPattern.semantics, post]

end narrowing_examples
