import Lean


/-
# Semantic framework

The framework supplies the denotational layer shared by all reasoning
procedures: state types, pattern semantics, and rule semantics. It does not
own equational theories or a particular unification algorithm.
-/
namespace framework

universe u v w x y

-- α is the type of states
class State (α : Type u) : Prop where

/-
## Patterns

All definitions whose primary purpose is to represent or compare patterns live
under this namespace. They are exported from `framework` below to preserve the
compact user-facing names used by existing models.
-/
namespace Patterns

/- ### Data Structure: Atomic Patterns -/
-- P is a type of atomic patterns denoting sets of α-states.
class APatt (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop -- read "P contains α"

/-- The body returned by a constrained pattern closure. -/
structure APattBody (α : Type u) where
  term : α -- TODO: require \a to be state
  requires : Prop := True -- TODO: rename it to cond

-- case 1: unconstrained ground terms (e.g., f(a,b) : APatt)
instance {α : Type u} [State α] : APatt α α where
  semantics p state := p = state

-- case 2:  constrained ground terms (e.g., ⟨f(a,b), a>b⟩ : APatt)
instance {α : Type u} [State α] : APatt α (APattBody α) where
  semantics p state := p.term = state ∧ p.requires

-- case 3) constrained terms w/ bound variables (e.g., λx.λy.⟨f(x,y), x>y⟩ : APatt)
instance {α : Type u} {A : Type v} {P : Type w}
    [State α] [APatt α P] : APatt α (A → P) where
  semantics p state := ∃ x, APatt.semantics (p x) state

/- ### Data Structure: Composite Patterns (via Disjunction) -/
/-- Patterns are atomic patterns closed under finite disjunction. -/
class Pattern (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

/-- A heterogeneous disjunction of two pattern representations. -/
structure Disjunction (P : Type v) (Q : Type w) where
  left : P
  right : Q

infixr:65 " ⊔ " => framework.Patterns.Disjunction.mk

/-- The empty pattern, used when narrowing returns no alternatives. -/
inductive EmptyPattern (α : Type u) where
  | empty : EmptyPattern α

-- case 1: atomic patterns
instance {α : Type u} {P : Type v}
    [State α] [APatt α P] :
    Pattern α P where
  semantics := APatt.semantics

-- case 2: disjuncted patterns
instance {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q] :
    Pattern α (Disjunction P Q) where
  semantics patterns state :=
    Pattern.semantics patterns.left state ∨
    Pattern.semantics patterns.right state

-- case 3: empty patterns
instance {α : Type u} [State α] :
    APatt α (EmptyPattern α) where
  semantics _ _ := False

/- ### Derived Notions -/
/-- Semantic inclusion between two possibly different pattern representations. -/
def Subsumes {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q]
    (source : P) (target : Q) : Prop :=
  ∀ state, Pattern.semantics source state →
    Pattern.semantics target state

infix:50 " ⊑ " => Subsumes

end Patterns


/-
## Rules

Rule representations and all judgments that fundamentally mention a rule live
under this namespace.
-/
namespace Rules

open Patterns

/- ### Data Structure: Rules -/
/-- The body returned by a constrained rewrite-rule closure. -/
structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  requires : Prop := True

-- TODO: rename it to just "Rule"
-- Atomic rules and their Lean closures denote binary transition relations.
class AtRule (α : outParam (Type u)) [State α] (R : Type v) where
  semantics : R → α → α → Prop

-- case 1: unquantified ground rules
instance {α : Type u} [State α] :
    AtRule α (RuleBody α) where
  semantics rule before after :=
    rule.lhs = before ∧ rule.rhs = after ∧ rule.requires

-- case 2: quantified rules
instance {α : Type u} {A : Type v} {R : Type w}
    [State α] [AtRule α R] : AtRule α (A → R) where
  semantics rule before after :=
    ∃ argument, AtRule.semantics (rule argument) before after

/- ### Derived Notions -/
/- used for defining narrowsTo -/
def postImage {α : Type u} {P : Type v} {R : Type w}
    [State α] [Pattern α P] [AtRule α R]
    (rule : R) (source : P) (after : α) : Prop :=
  ∃ before,
    Pattern.semantics source before ∧
    AtRule.semantics rule before after

-- TODO: NarrowsTo -> narrowsTo
/- R ⊢ P ↝ Q iff ∀ q ∈ Q, ∃ p ∈ P, R p q -/
def NarrowsTo {α : Type u} {P : Type v} {Post : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Post] [AtRule α R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after,
    Pattern.semantics post after ↔ postImage rule source after

notation:40 rule " ⊢ " source " ↝ " post =>
  NarrowsTo rule source post

/- R ⊢ P ↪ Q iff ∀ p,q ∈ α, p ∈ P → R p q → q ∈ Q -/
def mapsInto {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [AtRule α R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∀ before after,
    Pattern.semantics source before →
    AtRule.semantics rule before after →
    Pattern.semantics target after

notation:40 rule " ⊢ " source " ↪ " target =>
  mapsInto rule source target

/- ### Useful Lemmas -/
/-
  rule ⊢ source ↝ post
  post ⊑ target
  ────────────────────
  rule ⊢ source ↪ target
-/
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

/--
Prove `mapsInto` through an existentially generated post.  The post
representation itself is existential because a heterogeneous disjunction's
concrete Lean type is not known before narrowing.
  (∃ Post, ∃ postPattern, ∃ post)
  rule ⊢ source ↝ post
  post ⊑ target
  ─────────────────────────────
  rule ⊢ source ↪ target
-/
theorem mapsInto_via_narrowing
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [state : State α] [sourcePattern : Pattern α P]
    [targetPattern : Pattern α Q] [ruleSemantics : AtRule α R]
    {rule : R} {source : P} {target : Q}
    (decomposition :
      ∃ (Post : Type y) (postPattern : Pattern α Post) (post : Post),
        @NarrowsTo α P Post R state sourcePattern postPattern ruleSemantics
            rule source post ∧
        @Subsumes α Post Q state postPattern targetPattern post target) :
    mapsInto rule source target := by
  rcases decomposition with
    ⟨Post, postPattern, post, narrowing, subsumption⟩
  exact @mapsInto_of_narrowsTo_of_subsumes α P Post Q R
    state sourcePattern postPattern targetPattern ruleSemantics
    rule source post target narrowing subsumption

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

end Rules

-- Preserve the concise modelling API while keeping declaration ownership
-- visible in the namespace tree.
export Patterns (APatt APattBody Pattern Disjunction EmptyPattern Subsumes)
export Rules (RuleBody AtRule postImage NarrowsTo mapsInto
  mapsInto_of_narrowsTo_of_subsumes mapsInto_via_narrowing
  mapsInto_iff_subsumes_of_narrowsTo)

end framework


/-!
# Equational theories

A `Theory` is the declarative equality component shared by unification,
narrowing, and rewriting. It records term-forming symbols and proof-carrying
structural laws, but it does not choose an algorithm or contain rewrite rules.
Those are responsibilities of clients and of a future executable module.
-/
namespace Theory

universe u

/--
A structural algebraic law attached to the exact operation it describes.
Indexing by the operation prevents registering a proof about one symbol as a
law of another. Absence or combinations of laws are later classified as free,
A, C, AC, and related unification fragments.
-/
inductive OperatorLaw : {operationType : Type u} →
    (operation : operationType) → Type (u + 1) where
  | commutative {α : Type u} {operation : α → α → α}
      (proof : ∀ left right, operation left right = operation right left) :
      OperatorLaw operation
  | associative {α : Type u} {operation : α → α → α}
      (proof : ∀ first second third,
        operation (operation first second) third =
          operation first (operation second third)) :
      OperatorLaw operation

namespace OperatorLaw

/-!
Convenience constructors in this namespace turn standard Lean algebraic
instances into the proof-carrying laws stored by a theory.
-/

def commutativeOfInstance {α : Type u} (operation : α → α → α)
    [Std.Commutative operation] : OperatorLaw operation :=
  .commutative Std.Commutative.comm

def associativeOfInstance {α : Type u} (operation : α → α → α)
    [Std.Associative operation] : OperatorLaw operation :=
  .associative Std.Associative.assoc

end OperatorLaw

/-- One symbol of any arity; its complete signature is its inferred Lean type. -/
structure Symbol where
  {operationType : Type u}
  operation : operationType
  laws : List (OperatorLaw operation) := []

/-- Uniform declaration constructor for nullary through arbitrary-arity symbols. -/
def Symbol.declare {operationType : Type u} (operation : operationType)
    (laws : List (OperatorLaw operation) := []) : Symbol where
  operation := operation
  laws := laws

end Theory

universe theory_u

/-- The symbol signature and structural equality laws of a theory. -/
structure Theory where
  symbols : List (Theory.Symbol.{theory_u}) := []





open Lean Meta Elab Term Tactic
open framework framework.Patterns

/-
# Unification

Unification begins with semantic intersection of two pattern denotations and
computationally explains that intersection by a sound, complete set of
factorizing substitutions. The namespace separates semantic judgments,
solver-neutral certificates, theory-specific backends, and proof-state UI.
-/
namespace Unification

universe u v w

/- ## Unifiability -/

/- atomic unifiability (non-empty intersection) -/
def Unifiable {α : Type u} {P : Type v} {Q : Type w}
    [State α] [APatt α P] [APatt α Q]
    (p : P) (q : Q) : Prop :=
  ∃ state, APatt.semantics p state ∧ APatt.semantics q state

infix:50 " ⋈ " => Unifiable

/- unifiability modulo equational theory -/
def UnifiableIn {α : Type u} {P : Type v} {Q : Type w}
    [State α] [APatt α P] [APatt α Q]
    (_theory : Theory) (left : P) (right : Q) : Prop :=
  Unifiable left right

notation:50 left " ⋈[" theory "] " right =>
  UnifiableIn theory left right


/-
`Problem` defines a way to represent patterns as meta expressions
-/
-- TODO: move this as part of Pattern?
namespace Problem

/- transform patterns into meta objects. lambda binders get unwrapped. -/
-- rename: APattMeta
/- e.g., λx1. λx2. f x1 x2 is turned into: -/
structure SaturatedPattern where
  application : Expr -- e.g., f ?x1 ?x2
  arguments : Array Expr -- e.g., [?x1, ?x2]
  argumentNames : Array Name -- e.g., [x1, x2]

/- encodes the equation p1 = p2 for two patterns -/
-- rename: APattEq
structure Input where
  theory? : Option Expr := none
  lhs : SaturatedPattern
  rhs : SaturatedPattern

def visibleName (fallback : String) (name : Name) : Name :=
  if name.isAnonymous then Name.mkSimple fallback else name.eraseMacroScopes

/- Saturate all explicit arguments of a pattern closure. -/
-- rename: APatt2Meta
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

/-- Extract the optional theory and two patterns from a unifiability proposition. -/
def ofUnifiableType (type : Expr) : MetaM Input := do
  let type ← instantiateMVars type
  let arguments := type.getAppArgs
  let isDefault := type.getAppFn.isConstOf ``Unification.Unifiable
  let isTheoryIndexed :=
    type.getAppFn.isConstOf ``Unification.UnifiableIn
  unless (isDefault && arguments.size >= 2) ||
      (isTheoryIndexed && arguments.size >= 3) do
    throwError "expected a hypothesis of the form `p ⋈ q`"
  let lhs ← saturatePattern arguments[arguments.size - 2]!
  let rhs ← saturatePattern arguments[arguments.size - 1]!
  let theory? := if isTheoryIndexed then
      some arguments[arguments.size - 3]!
    else
      none
  return { theory?, lhs, rhs }

def argumentCount (problem : Input) : Nat :=
  problem.lhs.arguments.size + problem.rhs.arguments.size

def symbolicArguments (problem : Input) : Array Expr :=
  problem.lhs.arguments ++ problem.rhs.arguments

end Problem


/-
`Dispatch` interprets a declarative `Theory` only far enough to choose a
unification algorithm. It owns no symbols or laws: other reasoning procedures
may interpret the same theory through their own dispatch layers.

function `backend : Theory -> Backend`
determines which backend algorithm to use given a theory
-/
namespace Dispatch

inductive Backend where
  | free
  | c

/-- Read the structural-law kinds attached to one declared symbol. -/
private partial def scanLaws (laws : Expr)
    (foundAssociative foundCommutative : Bool) : MetaM (Bool × Bool) := do
  let laws ← withTransparency .all <| whnf laws
  let arguments := laws.getAppArgs
  if laws.getAppFn.isConstOf ``List.nil then
    return (foundAssociative, foundCommutative)
  unless laws.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce a symbol's structural-law declarations"
  let lawExpr := arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  let lawExpr ← withTransparency .all <| whnf lawExpr
  let isAssociative :=
    lawExpr.getAppFn.isConstOf ``Theory.OperatorLaw.associative
  let isCommutative :=
    lawExpr.getAppFn.isConstOf ``Theory.OperatorLaw.commutative
  unless isAssociative || isCommutative do
    throwError "the theory contains an unrecognized structural law"
  scanLaws tail (foundAssociative || isAssociative)
    (foundCommutative || isCommutative)

/-- Select a prototype backend from an arbitrary-arity symbol list. -/
private partial def scanSymbols (symbols : Expr) (foundC : Bool) : MetaM Backend := do
  let symbols ← withTransparency .all <| whnf symbols
  let arguments := symbols.getAppArgs
  if symbols.getAppFn.isConstOf ``List.nil then
    return if foundC then .c else .free
  unless symbols.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce the theory's symbol declarations"
  let symbol := arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  let laws ← mkAppM ``Theory.Symbol.laws #[symbol]
  let (hasAssociative, hasCommutative) ← scanLaws laws false false
  if hasAssociative && hasCommutative then
    throwError "the AC backend is not implemented in this prototype"
  if hasAssociative then
    throwError "the associative-unification backend is not implemented in this prototype"
  let foundC := foundC || hasCommutative
  scanSymbols tail foundC

def backend (theory : Expr) : MetaM Backend := do
  let symbols ← mkAppM ``Theory.symbols #[theory]
  scanSymbols symbols false

end Dispatch


namespace Certificate

/-!
`Certificate` is the solver-neutral contract between computation and proof.
It represents residual freedom with explicit basis variables and separately
records candidate data, soundness, completeness, and concrete factorization.
-/

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

/--
A computed solution set whose alternatives have each been checked to be
actual unifiers.  Soundness is backend-independent data even when the tactic
used to construct the proofs is theory-specific.
-/
structure SoundSolutionSet where
  solutionSet : SolutionSet
  soundnessPropositions : Array Expr
  soundnessProofs : Array Expr

/--
A sound solution set together with a user-supplied proof that every unifier
factors through one of its alternatives.
-/
structure ExactSolutionSet extends SoundSolutionSet where
  completenessProposition : Expr
  completenessProof : Expr

/-- A checked factorization disjunction specialized to one semantic witness. -/
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


namespace C

/-!
This portion of `C` defines the logical contract for an operation that is free
modulo commutativity. It is model-supplied recognition/proof data, distinct
from the orientation-enumerating C backend defined below.
-/

/--
A binary operation that is free modulo commutativity.

`Std.Commutative op` supplies the equation used to justify swapped terms.
`eq_iff` is the constructor-decomposition principle needed to prove that the
two orientations are complete.  Commutativity alone would not be sufficient:
for example, a constant operation is commutative but has many extra equations.
-/
class Operator {α : Type u} (op : α → α → α) extends Std.Commutative op where
  eq_iff (a b c d : α) :
    op a b = op c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)

end C


namespace Free

/-!
`Free` is the native free first-order backend. It asks Lean's unifier for a
candidate, abstracts residual metavariables into an explicit basis, and
returns solver-neutral substitution images without proving completeness.
-/

/-- A free-backend candidate represented through the common alternative interface. -/
structure Candidate where
  alternative : Certificate.Alternative
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
  for residual in residuals do
    let some _originalIndex := symbolicArguments.findIdx? fun argument =>
        argument.isMVar && argument.mvarId! == residual
      | throwError "native unification introduced an unexpected metavariable"
    let type ← instantiateMVars (← residual.getType)
    unless (← getMVars type).isEmpty do
      throwError "dependent basis types are outside the supported free fragment"
    basisTypes := basisTypes.push type

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
    }] }

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
Optional automation for a zero-result completeness goal. `simp_all` proves
direct constructor clashes. For occurs-check cycles, every constructor
equation is also mapped through `sizeOf`; generated inductive `SizeOf`
equations reduce to inconsistent natural-number constraints checked by
`omega`.
-/
def certifyFailureGoal : TacticM Unit := do
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


end Free


namespace C

/-!
The C backend is deliberately an adapter around the free backend. It expands
the right-hand term into every orientation permitted by registered
`C.Operator`s, invokes native free unification independently on each
orientation, and returns the resulting finite candidate set through the
common `Certificate` interface.
-/

abbrev Candidate := Free.Candidate

structure Output where
  candidates : Array Candidate := #[]

private def operatorInstance? (operation : Expr) : MetaM (Option Expr) := do
  try
    return some (← synthInstance (← mkAppM ``Operator #[operation]))
  catch _ =>
    return none

private def pushUniqueExpr (expressions : Array Expr) (expression : Expr) :
    Array Expr :=
  if expressions.any fun existing => existing == expression then
    expressions
  else
    expressions.push expression

/--
Expose definitions until either a registered C operation or a rigid term is
visible.  Registered defined functions are kept opaque at their application
head so their user-supplied theory is not lost by unfolding.
-/
partial def exposeHead (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData
  match expression with
  | .app (.app operation _) _ =>
      if (← operatorInstance? operation).isSome then
        return expression
  | _ => pure ()
  let reduced ← withTransparency .all <| whnf expression
  if reduced == expression then
    return expression
  exposeHead reduced

/-- Enumerate all terms obtained by independently swapping registered C nodes. -/
private partial def orientations (expression : Expr) : MetaM (Array Expr) := do
  let expression ← exposeHead expression
  match expression with
  | .app (.app operation left) right =>
      if (← operatorInstance? operation).isSome then
        let leftOrientations ← orientations left
        let rightOrientations ← orientations right
        let mut result := #[]
        for left in leftOrientations do
          for right in rightOrientations do
            result := pushUniqueExpr result (mkApp2 operation left right)
            result := pushUniqueExpr result (mkApp2 operation right left)
        return result
  | _ => pure ()

  -- A C node may occur below an otherwise free application.
  let mut applications := #[expression.getAppFn]
  for argument in expression.getAppArgs do
    let argumentOrientations ← orientations argument
    let mut next := #[]
    for application in applications do
      for orientedArgument in argumentOrientations do
        next := pushUniqueExpr next (mkApp application orientedArgument)
    applications := next
  return applications

private def sameAlternative
    (left right : Certificate.Alternative) : Bool :=
  left.basisTypes == right.basisTypes && left.images == right.images

private def pushUniqueCandidate
    (candidates : Array Candidate) (candidate : Candidate) : Array Candidate :=
  if candidates.any fun existing =>
      sameAlternative existing.alternative candidate.alternative then
    candidates
  else
    candidates.push candidate

/--
Compute a finite candidate set of C-unifiers by reducing each C orientation to
the free solver. `withoutModifyingState` is essential:
native unification may assign the saturated metavariables, and every
orientation must start from the same untouched problem.
-/
def solve (problem : Problem.Input) : MetaM Output := do
  let rhsOrientations ← orientations problem.rhs.application
  let mut candidates := #[]
  for rhs in rhsOrientations do
    let output ← withoutModifyingState do
      Free.solve {
        lhs := problem.lhs
        rhs := { problem.rhs with application := rhs }
      }
    for candidate in output.candidates do
      candidates := pushUniqueCandidate candidates candidate
  return { candidates }

end C


namespace Exposure

/-!
`Exposure` is the proof-state view of a certified solution set. It introduces
stable basis names and factorization equations for users; it is unrelated to
the equational `Theory` that selected the solver.
-/

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

end Exposure


namespace Tactic

/-!
`Tactic` orchestrates the complete user command: parse the semantic problem,
run a selected backend, check candidate soundness, emit completeness, and use
`Exposure` to open the certified alternatives. It is the main replaceable
frontend/backend boundary.
-/

private structure SemanticWitnesses where
  actualArguments : Array Expr
  stateId : FVarId
  lhsSemanticsId : FVarId
  rhsSemanticsId : FVarId
  equalityId : FVarId

private def instantiateSaturatedApplication
    (pattern : Problem.SaturatedPattern) (arguments : Array Expr) : Expr :=
  pattern.application.replace fun subterm =>
    match subterm with
    | .mvar id =>
        match pattern.arguments.findIdx? fun argument =>
            argument.isMVar && argument.mvarId! == id with
        | some index => arguments[index]?
        | none => none
    | _ => none

private def instantiateOriginalArguments
    (expression : Expr) (originals replacements : Array Expr) : Expr :=
  expression.replace fun subterm =>
    match subterm with
    | .mvar id =>
        match originals.findIdx? fun original =>
            original.isMVar && original.mvarId! == id with
        | some index => replacements[index]?
        | none => none
    | _ => none

private partial def withOriginalArguments
    {α : Type}
    (problem : Problem.Input) (index : Nat) (arguments : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  let originals := Problem.symbolicArguments problem
  if _h : index < originals.size then
    let original := originals[index]!
    let type ← inferType original
    let type := instantiateOriginalArguments type originals arguments
    let names := problem.lhs.argumentNames ++ problem.rhs.argumentNames
    let name := Problem.visibleName s!"x{index + 1}" names[index]!
    withLocalDeclD name type fun argument =>
      withOriginalArguments problem (index + 1) (arguments.push argument)
        continuation
  else
    continuation arguments

private partial def withBasisArguments
    {α : Type}
    (types : Array Expr) (index : Nat) (arguments : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun argument =>
        withBasisArguments types (index + 1) (arguments.push argument)
          continuation
  else
    continuation arguments

private def equationType
    (problem : Problem.Input) (arguments : Array Expr) : MetaM Expr := do
  unless arguments.size == Problem.argumentCount problem do
    throwError "a unification certificate has the wrong number of arguments"
  let lhsArguments := arguments.extract 0 problem.lhs.arguments.size
  let rhsArguments := arguments.extract problem.lhs.arguments.size arguments.size
  let lhs ← C.exposeHead
    (instantiateSaturatedApplication problem.lhs lhsArguments)
  let rhs ← C.exposeHead
    (instantiateSaturatedApplication problem.rhs rhsArguments)
  mkEq lhs rhs

/-- State that every actual unifier factors through a returned alternative. -/
private def completenessType
    (problem : Problem.Input) (solutionSet : Certificate.SolutionSet) : MetaM Expr :=
  withOriginalArguments problem 0 #[] fun arguments => do
    let equation ← equationType problem arguments
    let (_, factorization) ←
      Certificate.solutionSetType solutionSet arguments
    let body ← mkArrow equation factorization
    mkForallFVars arguments body

/-- State that every basis instance of one returned alternative is a unifier. -/
private def soundnessType
    (problem : Problem.Input) (alternative : Certificate.Alternative) : MetaM Expr :=
  withBasisArguments alternative.basisTypes 0 #[] fun basis => do
    let mut images := #[]
    for image in alternative.images do
      images := images.push (← whnf
        (Certificate.instantiateImage image basis))
    let equation ← equationType problem images
    mkForallFVars basis equation

private def proveSoundness
    (ref : Syntax) (problem : Problem.Input)
    (solutionSet : Certificate.SolutionSet) (hypothesisId : FVarId) : TacticM
      Certificate.SoundSolutionSet := do
  let originalGoal ← getMainGoal
  let mut propositions := #[]
  let mut proofs := #[]
  for alternative in solutionSet.alternatives do
    let proposition ← originalGoal.withContext do
      soundnessType problem alternative
    let proof ← originalGoal.withContext do
      mkFreshExprMVar (some proposition)
    let soundnessGoal ← proof.mvarId!.clear hypothesisId
    replaceMainGoal [soundnessGoal]
    try
      evalTactic (← `(tactic|
        intros <;> simp_all [C.Operator.eq_iff] <;> grind))
    catch exception =>
      throwErrorAt ref m!"failed to certify a computed unifier's soundness:\n{exception.toMessageData}"
    unless ← proof.mvarId!.isAssigned do
      throwErrorAt ref "failed to construct a unifier soundness proof"
    propositions := propositions.push proposition
    proofs := proofs.push (← instantiateMVars proof)
    setGoals [originalGoal]
  return {
    solutionSet
    soundnessPropositions := propositions
    soundnessProofs := proofs
  }

private def exposeSemantics
    (ref : Syntax) (h : Ident) (problem : Problem.Input) : TacticM
      SemanticWitnesses := do
  let stateIdent ← Exposure.freshVisibleIdent ref `_unifyState
  let lhsIdent ← Exposure.freshVisibleIdent ref `_unifyLhs
  let rhsIdent ← Exposure.freshVisibleIdent ref `_unifyRhs
  evalTactic (← `(tactic|
    rcases ($h:term) with
      ⟨$stateIdent:ident, $lhsIdent:ident, $rhsIdent:ident⟩))

  let mut actualIdents := #[]
  for i in [:problem.lhs.arguments.size] do
    let base := Problem.visibleName s!"x{i + 1}"
      problem.lhs.argumentNames[i]!
    let argumentIdent ← Exposure.freshVisibleIdent ref base
    evalTactic (← `(tactic|
      rcases ($lhsIdent:term) with ⟨$argumentIdent:ident, $lhsIdent:ident⟩))
    actualIdents := actualIdents.push argumentIdent
  for i in [:problem.rhs.arguments.size] do
    let base := Problem.visibleName s!"y{i + 1}"
      problem.rhs.argumentNames[i]!
    let argumentIdent ← Exposure.freshVisibleIdent ref base
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
    unless proofType.eq?.isSome do
      throwError "malformed atomic-pattern semantics"
    let lhsArguments := actualArguments.extract 0 problem.lhs.arguments.size
    let rhsArguments := actualArguments.extract problem.lhs.arguments.size
      actualArguments.size
    -- Rebuild the equation from the saturated closures instead of reading its
    -- sides back from `proof`.  The latter may already have unfolded a
    -- reducible registered operation while reducing `APatt.semantics`.
    let lhs ← C.exposeHead
      (instantiateSaturatedApplication problem.lhs lhsArguments)
    let rhs ← C.exposeHead
      (instantiateSaturatedApplication problem.rhs rhsArguments)
    return (← mkEq lhs rhs, proof)
  let (equalityId, goal) ← goal.withContext do
    goal.note equalityName equalityProof (some equalityType)
  setGoals [goal]

  return {
    actualArguments
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

/--
Shared frontend/backend boundary.  A backend computes alternatives; their
soundness is checked immediately, while completeness becomes an explicit
user-level proof goal.  Result goals depend on that completeness certificate.
-/
private def runWith {Output : Type}
    (solve : Problem.Input → MetaM Output)
    (solutions : Output → Certificate.SolutionSet)
    (ref : Syntax) (h : Ident) : TacticM Unit := do
  let hypothesisId ← getFVarId h
  let hypothesisType ← instantiateMVars (← hypothesisId.getType)
  let initialGoal ← getMainGoal
  let (problem, output) ← initialGoal.withContext do
    let problem ← Problem.ofUnifiableType hypothesisType
    let output ← solve problem
    return (problem, output)

  let sound ← proveSoundness ref problem (solutions output) hypothesisId
  let completenessProposition ← initialGoal.withContext do
    completenessType problem sound.solutionSet
  let completenessName ← initialGoal.withContext do
    return (← getLCtx).getUnusedName `completeness
  let completenessValue ← initialGoal.withContext do
    mkFreshExprMVar (some completenessProposition)
  let completenessGoal ← completenessValue.mvarId!.clear hypothesisId
  completenessGoal.setTag `completeness
  let continuationGoal ← initialGoal.withContext do
    initialGoal.assert completenessName completenessProposition completenessValue
  let (completenessId, continuationGoal) ← continuationGoal.withContext do
    continuationGoal.intro1P
  let completenessProof := mkFVar completenessId

  setGoals [continuationGoal]
  let witnesses ← exposeSemantics ref h problem
  let goal ← getMainGoal
  let (branchPropositions, proposition, proof) ← goal.withContext do
    let (branchPropositions, proposition) ←
      Certificate.solutionSetType sound.solutionSet witnesses.actualArguments
    let specialized := mkAppN completenessProof witnesses.actualArguments
    let proof := mkApp specialized (mkFVar witnesses.equalityId)
    let proofType ← inferType proof
    unless ← isDefEq proofType proposition do
      throwError "the completeness certificate does not match the computed solution set"
    return (branchPropositions, proposition, proof)
  let exact : Certificate.ExactSolutionSet := {
    sound with
    completenessProposition
    completenessProof
  }
  let proven : Certificate.ProvenSolutionSet := {
    solutionSet := exact.solutionSet
    branchPropositions
    proposition
    proof
  }
  Exposure.expose proven
  clearSemantics witnesses
  let resultGoals ← getGoals
  setGoals (completenessGoal :: resultGoals)

/-- Compute a free solution set and expose completeness plus result goals. -/
def run (ref : Syntax) (h : Ident) : TacticM Unit :=
  runWith Free.solve
    (fun output => {
      alternatives := output.candidates.map (·.alternative)
    })
    ref h

/-- Compute a C solution set and expose completeness plus result goals. -/
def runC (ref : Syntax) (h : Ident) : TacticM Unit :=
  runWith C.solve
    (fun output => {
      alternatives := output.candidates.map (·.alternative)
    })
    ref h

/--
Resolve an explicit equational theory from an indexed unifiability hypothesis
and dispatch to the prototype backend selected by its structural laws.
-/
def runIn (ref : Syntax) (h : Ident) (theorySyntax : TSyntax `term) :
    TacticM Unit := do
  let hypothesisId ← getFVarId h
  let hypothesisType ← instantiateMVars (← hypothesisId.getType)
  let goal ← getMainGoal
  let problem ← goal.withContext do
    Problem.ofUnifiableType hypothesisType
  let some declaredTheory := problem.theory?
    | throwErrorAt h "`unify ... in ...` requires a hypothesis `p ⋈[T] q`"
  let requestedTheory ← goal.withContext do
    Term.elabTerm theorySyntax.raw
      (some (← inferType declaredTheory))
  let theoriesMatch ← goal.withContext do
    withoutModifyingState
      (isDefEq requestedTheory declaredTheory)
  unless theoriesMatch do
    throwErrorAt theorySyntax
      "the requested theory does not match the theory in the hypothesis"
  match ← goal.withContext do
      Dispatch.backend requestedTheory with
  | .free => run ref h
  | .c => runC ref h

end Tactic


namespace Completeness

/-!
`Completeness` provides optional automation for the ordinary proof obligation
emitted by `unify`. It does not belong to a solver and may be replaced by a
manual proof or a theory-specific certificate checker.
-/

/--
Optional user-level automation for the completeness goal emitted by `unify`.
The goal remains an ordinary proposition: users may replace this tactic with
any manual, theory-specific, or externally checked proof.
-/
def run : TacticM Unit := do
  evalTactic (← `(tactic| intros))
  try
    evalTactic (← `(tactic|
      solve | (simp_all <;> grind)))
  catch _ => pure ()
  if (← getGoals).isEmpty then
    return
  try
    evalTactic (← `(tactic|
      solve | (simp_all [C.Operator.eq_iff] <;> grind)))
  catch _ => pure ()
  if (← getGoals).isEmpty then
    return
  Free.certifyFailureGoal

end Completeness

end Unification

/--
Compute the free first-order solution set for `h`, check candidate soundness,
and expose completeness followed by one result goal per candidate.
-/
elab "unify " h:ident : tactic =>
  Unification.Tactic.run h.raw h

/--
Compute all candidates modulo registered free commutative operations, check
their soundness, and expose completeness followed by the result goals.
-/
elab "c_unify " h:ident : tactic =>
  Unification.Tactic.runC h.raw h

/-- Unify using the equational theory explicitly named by the user. -/
elab "unify " h:ident " in " theory:term : tactic =>
  Unification.Tactic.runIn h.raw h theory

/-- Attempt to discharge the explicit completeness goal emitted by `unify`. -/
elab "unify_complete" : tactic =>
  Unification.Completeness.run


namespace Narrowing

/-!
`Narrowing` is an adapter around the generic unification API.  It extracts the
structural equation between a rule LHS and a source-pattern term, delegates
that equation to a backend, and reconnects the candidate substitutions to the
rule RHS and both constraints.
-/

namespace Problem

/-!
`Narrowing.Problem` projects a rule closure and constrained source closure,
saturates their shared variables once, and forms the structural equation
`rule.lhs = source.term` consumed by unification.
-/

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
      lhs := ← project ``framework.Rules.RuleBody.lhs application
      rhs := ← project ``framework.Rules.RuleBody.rhs application
      requires := ← project ``framework.Rules.RuleBody.requires application
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
      term := ← project ``framework.Patterns.APattBody.term application
      requires := ← project ``framework.Patterns.APattBody.requires application
    }
  catch _ =>
    throwError "`narrow` expects a closure returning `APattBody`"

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

/-!
`Goal` recognizes the semantic goal shapes manipulated by narrowing-side
automation. It extracts user objects without deciding how their propositions
will be proved.
-/

/-- The two user objects encoded in a `Subsumes` target. -/
structure SubsumptionInput where
  source : Expr
  target : Expr

def ofSubsumesType (type : Expr) : MetaM SubsumptionInput := do
  let type ← instantiateMVars type
  let arguments := type.getAppArgs
  unless type.getAppFn.isConstOf ``framework.Patterns.Subsumes &&
      arguments.size >= 2 do
    throwError "`subsume` expects a goal of the form `source ⊑ target`"
  return {
    source := arguments[arguments.size - 2]!
    target := arguments[arguments.size - 1]!
  }

end Goal


namespace Backend

/-!
`Backend` is the narrow bridge from a narrowing problem to the common
unification solution-set format. Theory-specific dispatch can later replace
this free-only bridge without affecting successor construction.
-/

/--
The current backend bridge.  Backend-private evidence is erased here; all
later narrowing phases consume only the common solver-neutral solution set.
-/
def solve (problem : Problem.Input) : MetaM Unification.Certificate.SolutionSet := do
  let output ← Unification.Free.solve problem.unification
  return { alternatives := output.candidates.map (·.alternative) }

end Backend


namespace Materialization

/-!
`Materialization` turns each substitution alternative into a constrained
successor by applying it to the rule RHS and both conditions, then combines
all successors into the generated post pattern.
-/

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
    whnf (← mkAppM ``framework.Rules.RuleBody.rhs #[ruleValue])
  let ruleRequires ← withTransparency .all <|
    whnf (← mkAppM ``framework.Rules.RuleBody.requires #[ruleValue])
  let sourceRequires ← withTransparency .all <|
    whnf (← mkAppM ``framework.Patterns.APattBody.requires #[sourceValue])
  return (rhs, sourceRequires, ruleRequires)

/-- Turn one backend alternative into its constrained successor closure. -/
def successor (problem : Problem.Input)
    (alternative : Unification.Certificate.Alternative) : MetaM Expr := do
  withBasisVariables alternative.basisTypes 0 #[] fun basis => do
    let (rhs, sourceRequires, ruleRequires) ←
      projections problem alternative basis
    let requires ← mkAppM ``And #[sourceRequires, ruleRequires]
    let body ← mkAppM ``framework.Patterns.APattBody.mk #[rhs, requires]
    mkLambdaFVars basis body

private def empty (problem : Problem.Input) : MetaM Expr := do
  let stateType ← inferType problem.rule.lhs
  let .sort (.succ level) ← whnf (← inferType stateType)
    | throwError "the narrowing state is not a type"
  return mkApp
    (mkConst ``framework.Patterns.EmptyPattern.empty [level]) stateType

private def disjoin (left right : Expr) : MetaM Expr :=
  mkAppM ``framework.Patterns.Disjunction.mk #[left, right]

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


namespace Closure

/-!
`Closure` discovers which user definitions should be unfolded while replaying
semantic proofs. It is proof-support machinery and does not participate in
unification or successor computation.
-/

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

def unfoldingDefinitions (expressions : Array Expr) : CoreM (Array Name) := do
  let environment ← getEnv
  let mut result := #[]
  for expression in expressions do
    let some name := closureDefinition? expression | continue
    let isDefinition := match environment.find? name with
      | some (.defnInfo _) | some (.opaqueInfo _) => true
      | _ => false
    if isDefinition && !result.contains name then
      result := result.push name
  return result

end Closure


namespace Certification

/-!
`Certification` proves that a materialized post is exactly the semantic
one-step image. This obligation is separate from structural unifier
certification because it also accounts for rule RHSs and constraints.
-/

/--
Certify that the materialized post is the complete one-step image.  This
prototype replays free constructor reasoning with `simp` and `grind`; an AC
backend can replace this namespace with certificate replay for its theory.
-/
def prove (ref : Syntax) (rule source : Expr)
    (ruleSyntax sourceSyntax : TSyntax `term) (postIdent : Ident) :
    TacticM Ident := do
  let narrowingIdent ←
    Unification.Exposure.freshVisibleIdent ref `narrowing
  let unfoldNames ← Closure.unfoldingDefinitions #[rule, source]
  let unfoldSimps ← unfoldNames.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
  try
    evalTactic (← `(tactic|
      have $narrowingIdent:ident :
          framework.Rules.NarrowsTo
            $ruleSyntax $sourceSyntax ($postIdent:term) := by
        simp [framework.Rules.NarrowsTo, framework.Rules.postImage,
          framework.Patterns.Pattern.semantics,
          framework.Patterns.APatt.semantics,
          framework.Rules.AtRule.semantics,
          $postIdent:term, $unfoldSimps,*] <;>
          grind))
  catch exception =>
    throwErrorAt ref m!"failed to certify the generated narrowing post:\n{exception.toMessageData}"
  return narrowingIdent

end Certification


namespace Tactic

/-!
`Narrowing.Tactic` connects post computation to the existential decomposition
created by `mapsInto_via_narrowing`. It binds the generated `post` and leaves
only semantic subsumption to the surrounding proof.
-/

private def ensureDecompositionGoal (goal : MVarId) : MetaM Unit := do
  let type ← whnf (← goal.getType)
  unless type.getAppFn.isConstOf ``Exists do
    throwError "`narrow` expects the post goal from `apply mapsInto_via_narrowing`"

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
Generate and bind the exact one-step post, then fill the post and narrowing
parts of the explicit decomposition.  Only subsumption remains.
-/
def run (ref : Syntax) (ruleSyntax sourceSyntax : TSyntax `term) : TacticM Unit := do
  let initialGoal ← getMainGoal
  let (rule, source, generatedPost) ← initialGoal.withContext do
    ensureDecompositionGoal initialGoal
    let rule ← Tactic.elabTerm ruleSyntax.raw none
    let source ← Tactic.elabTerm sourceSyntax.raw none
    let problem ← Problem.ofTerms rule source
    let solutionSet ← Backend.solve problem
    let generatedPost ← Materialization.post problem solutionSet.alternatives
    return (rule, source, generatedPost)

  let postIdent ← bindPost ref generatedPost
  let narrowingIdent ← Certification.prove ref rule source
    ruleSyntax sourceSyntax postIdent

  evalTactic (← `(tactic|
    refine ⟨_, inferInstance, $postIdent:term,
      $narrowingIdent:term, ?_⟩))

end Tactic


namespace Subsumption

/-!
`Subsumption` is the current lightweight prover for the residual inclusion
between the generated post and the user's target pattern. Its semantic goal
is stable even if stronger constraint automation replaces this prototype.
-/

/-- Simplify and prove the residual semantic inclusion between patterns. -/
def run : TacticM Unit := do
  let goal ← getMainGoal
  let input ← goal.withContext do
    Goal.ofSubsumesType (← goal.getType)
  let unfoldNames ← Closure.unfoldingDefinitions #[input.source, input.target]
  let unfoldSimps ← unfoldNames.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
  evalTactic (← `(tactic|
    simp [framework.Patterns.Subsumes,
      framework.Patterns.Pattern.semantics,
      framework.Patterns.APatt.semantics,
      $unfoldSimps,*] <;>
      grind))

end Subsumption

end Narrowing

/-- Generate the post and certify one constrained narrowing phase. -/
elab "narrow " rule:term " against " source:term : tactic =>
  Narrowing.Tactic.run rule.raw rule source

/-- Prove the residual pattern-subsumption phase. -/
elab "subsume" : tactic =>
  Narrowing.Subsumption.run










namespace examples

/-!
These user-level examples exercise free unification independently of rules.
They deliberately appear after all tactic code so the implementation cannot
depend on their particular model, patterns, or names.
-/

open framework

-- User-defined model for the examples.  It is deliberately not part of the
-- generic free-unification implementation, and it needs no `var` constructor.
inductive Conf where
  | c : Conf
  | f : Conf → Conf → Conf
  deriving Repr

instance : State Conf := ⟨⟩

/-- An empty theory: every symbol is free. -/
def FreeTheory : Theory := {}

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
  -- Completeness is an ordinary user-level goal.  It can be proved directly;
  -- `unify_complete` is merely optional automation for proofs like this one.
  · intros <;> simp_all
  · guard_hyp u1 : Conf
    guard_hyp h1 : x1 = f u1 c
    guard_hyp h2 : x2 = c
    guard_hyp h3 : y1 = u1
    exact True.intro

-- The explicit-theory form has the same public result interface.
example (h : pat1 ⋈[FreeTheory] pat2) : True := by
  unify h in FreeTheory
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : x1 = f u1 c
    guard_hyp h2 : x2 = c
    guard_hyp h3 : y1 = u1
    exact True.intro


-- non-unifiable example
example (h : (fun x : Conf => f x x) ⋈ c) : False := by
  unify h
  unify_complete

-- Failure produces a proof of `False`, so it closes an arbitrary target rather
-- than relying on the target itself being syntactically `False`.
example (h : (c : Conf) ⋈ f c c) : (0 : Nat) = 1 := by
  unify h
  unify_complete


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
  · unify_complete
  · guard_hyp u1 : Conf
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
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : a = u1
    guard_hyp h2 : b = c
    guard_hyp h3 : m = u1
    exact True.intro


-- Pure variables still produce a basis rather than an object-language `var`.
example (h : (fun left : Conf => left) ⋈ (fun right : Conf => right)) : True := by
  unify h
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : left = u1
    guard_hyp h2 : right = u1
    exact True.intro


-- A deeper cascading substitution exercises native unification and certificate
-- reconstruction independently of any declaration names.
example
    (h : (fun a b d : Conf => f a (f b d)) ⋈
      (fun x : Conf => f (f x c) (f c x))) : True := by
  unify h
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : a = f u1 c
    guard_hyp h2 : b = c
    guard_hyp h3 : d = u1
    guard_hyp h4 : x = u1
    exact True.intro


-- A ground unification example
example (h : (f c c : Conf) ⋈ f c c) : True := by
  unify h
  · unify_complete
  · exact True.intro


-- An occurs-check failure: the constructor equations would imply
-- `y = f y c`, which no finite `Conf` can satisfy.
example
    (h : (fun x : Conf => f x x) ⋈
      (fun y : Conf => f (f y c) y)) : False := by
  unify h
  unify_complete


end examples


namespace narrowing_examples

/-!
These examples define an independent user model, constrained patterns, and
rules to demonstrate exact one-step post generation followed by subsumption.
They are clients of both the semantic framework and unification result format.
-/

open framework

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
def source (n : Nat) : APattBody Conf where
  term := pair (atom 0) (atom n)
  requires := 0 < n

/-- `pair (atom payload) (atom (payload + 1))` where `payload > 0` -/
def target (payload : Nat) : APattBody Conf where
  term := pair (atom payload) (atom (payload + 1))
  requires := 0 < payload

/-  rl : pair (atom 0) (atom payload)
 => pair (atom payload) (atom next)
 if next = payload + 1` -/
def advance (payload next : Nat) : RuleBody Conf where
  lhs := pair (atom 0) (atom payload)
  rhs := pair (atom payload) (atom next)
  requires := next = payload + 1

-- This is exactly the structural equation used by `narrow`: the rule's two
-- closure arguments come first, followed by the source closure's argument.
-- Its two basis variables become the two binders of the generated `post`.
example
    (h :
      (fun payload next : Nat => (advance payload next).lhs) ⋈
      (fun n : Nat => (source n).term)) : True := by
  unify h
  · unify_complete
  · guard_hyp u1 : Nat
    guard_hyp u2 : Nat
    guard_hyp h1 : payload = u1
    guard_hyp h2 : next = u2
    guard_hyp h3 : n = u1
    -- Substitution in `advance.rhs` gives
    -- `pair (atom u1) (atom u2)`.  Substitution in the source and rule
    -- constraints gives `0 < u1 ∧ u2 = u1 + 1`, exactly the body of `post`
    -- generated by the following narrowing example.
    exact True.intro

example : advance ⊢ source ↪ target := by
  apply mapsInto_via_narrowing
  narrow advance against source
  subsume

/-- A rule whose constructor-headed LHS cannot match `source`. -/
def blocked : RuleBody Conf where
  lhs := pair (atom 1) (atom 0)
  rhs := atom 0

-- With no structural unifier, `narrow` generates the empty post and
-- `subsume` closes its inclusion. No special lemma about `blocked` is supplied.
example : blocked ⊢ source ↪ target := by
  apply mapsInto_via_narrowing
  narrow blocked against source
  subsume

/- This LHS matches `source`, but its constraint requires the matched positive
payload to be zero. -/
def constrainedOut (payload : Nat) : RuleBody Conf where
  lhs := pair (atom 0) (atom payload)
  rhs := atom payload
  requires := payload = 0

-- Structural unification returns an MGU branch.  Its instantiated constraints
-- are `0 < n` and `payload = 0`, so the constraints filter that branch out.
example : constrainedOut ⊢ source ↪ target := by
  apply mapsInto_via_narrowing
  narrow constrainedOut against source
  subsume

end narrowing_examples







namespace c_unification_examples

/-!
These examples provide a user-defined free-commutative operation and a theory
that registers its structural law. They demonstrate multi-MGU exposure through
the same interface as free unification.
-/

open framework

/-!
`Conf` has the same shape as an ordinary user model: it contains only concrete
configuration constructors and no constructor for logical variables.  The
commutative `f` is a separate function symbol rather than an ordered inductive
constructor.  Its equational laws are part of this example model, not the
tactic, and all tactic code still appears above these declarations.
-/

inductive Conf where
  | atom : Nat → Conf
  | g : Conf → Conf → Conf
  deriving Repr

instance : State Conf := ⟨⟩

-- A function symbol of the model.  It is deliberately not a `Conf`
-- constructor, so its commutativity does not conflict with constructor
-- injectivity.
axiom f : Conf → Conf → Conf

/-- The characteristic equality law of a free commutative constructor. -/
axiom f_eq_iff (a b c d : Conf) :
  f a b = f c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)

axiom f_comm (a b : Conf) : f a b = f b a

/-- Register `f`; `c_unify` discovers this instance by typeclass synthesis. -/
instance : Unification.C.Operator f where
  comm := f_comm
  eq_iff := f_eq_iff

/-!
`Theory1` registers `f` with the same declaration function used for every arity.
Only the commutative law is binary-specific. The ordinary constructor `g`
is absent and is therefore free.
-/
noncomputable def Theory1 : Theory where
  symbols := [Theory.Symbol.declare f [
    .commutative f_comm
  ]]

noncomputable def combineThree (first second third : Conf) : Conf :=
  Conf.g (Conf.g first second) third

/-- One uniform list containing unary, free binary, C, and ternary symbols. -/
noncomputable def MixedTheory : Theory where
  symbols := [
    Theory.Symbol.declare Conf.atom,
    Theory.Symbol.declare Conf.g,
    Theory.Symbol.declare f [.commutative f_comm],
    Theory.Symbol.declare combineThree
  ]

-- The same registration is visible to standard Lean tooling.
example (a b : Conf) : f a b = f b a := by
  exact Std.Commutative.comm a b

noncomputable def pairLeft (x y : Conf) : Conf := f x y
noncomputable def pairRight (a b : Conf) : Conf := f a b

#print pairLeft
#print pairRight

-- There are two MGUs: the direct pairing and the swapped pairing.  Each is
-- exposed through exactly the same basis-variable/equation interface as the
-- free `unify` tactic, so this proof receives two goals.
example (h : pairLeft ⋈[Theory1] pairRight) : True := by
  unify h in Theory1
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp u2 : Conf
    guard_hyp h1 : x = u1
    guard_hyp h2 : y = u2
    guard_hyp h3 : a = u1
    guard_hyp h4 : b = u2
    exact True.intro
  · guard_hyp u1 : Conf
    guard_hyp u2 : Conf
    guard_hyp h1 : x = u1
    guard_hyp h2 : y = u2
    guard_hyp h3 : a = u2
    guard_hyp h4 : b = u1
    exact True.intro

-- The same C dispatch works when unrelated symbols of other arities share the
-- theory. Registration does not partition symbols by arity.
example (h : pairLeft ⋈[MixedTheory] pairRight) : True := by
  unify h in MixedTheory
  · unify_complete
  all_goals exact True.intro

-- Registration is recursive: independently swapping the outer and inner
-- occurrences yields a finite complete set, and every MGU becomes one goal.
example
    (h :
      (fun x y z : Conf => f (f x y) z) ⋈[Theory1]
      (fun a b c : Conf => f c (f a b))) : True := by
  unify h in Theory1
  · unify_complete
  all_goals exact True.intro

-- Free constants can rule out every direct/swapped branch.  The hypothesis is
-- then contradictory and `c_unify` closes an arbitrary target.
open Conf

def red : Conf := atom 0
def blue : Conf := atom 1

@[simp] theorem red_ne_blue : red ≠ blue := by
  simp [red, blue]

example (h : (f red red : Conf) ⋈[Theory1] f red blue) : False := by
  unify h in Theory1
  unify_complete

end c_unification_examples


namespace theory_examples

/-!
These declarations demonstrate that theories register symbols uniformly
across arities and sorts. They exercise only the declarative theory interface,
not a particular user model or unification proof.
-/

/-- Representative operations of several arities and sorts. -/
def zeroSymbol : Nat := 0
def increment (value : Nat) : Nat := value + 1
def firstOfThree (first _second _third : Nat) : Nat := first
def select (value : Nat) (enabled : Bool) : Nat :=
  if enabled then value else 0

/--
All arities use the same declaration function.  `select` also demonstrates
that argument sorts need not be homogeneous.
-/
def MixedArityFree : Theory where
  symbols := [
    Theory.Symbol.declare zeroSymbol,
    Theory.Symbol.declare increment,
    Theory.Symbol.declare firstOfThree,
    Theory.Symbol.declare select
  ]

/- `Nat.add` needs no new law proofs: its existing theorems populate the
operator-law list. This declaration does not claim that AC is the full
arithmetic theory; it selects the theory used for unification. -/
def NatAC : Theory where
  symbols := [Theory.Symbol.declare Nat.add [
    .associative Nat.add_assoc,
    .commutative Nat.add_comm
  ]]

end theory_examples
