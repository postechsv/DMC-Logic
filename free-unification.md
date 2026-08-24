# Certified free unification and narrowing in Lean

This document explains the prototype implemented in `free-unification.lean`.
It is written top-down: first the mathematical idea and the public proof
experience, then the orchestration layer, and finally the individual solver
and certification components.

The main design objective is:

> Compute unifiers using a replaceable backend, but expose only a stable,
> proof-producing interface consisting of basis variables, substitution
> equations, and possibly several alternatives.

The current implementation includes:

- semantic constrained patterns represented by ordinary Lean closures;
- a certified free-unification tactic based on Lean's native unifier;
- a prototype unifier for free commutative symbols;
- a uniform, arbitrary-arity equational-module interface;
- one-step constrained narrowing built as a client of the unification result
  format; and
- subsumption automation for completing simple reachability proofs.

The state type defined by a user contains only model values. It does **not**
need an object-language constructor such as `var`. Logical variables are Lean
binders in pattern and rule closures, while basis variables are fresh Lean
locals produced by the tactic.

---

## 1. High-level overview

### 1.1 Conceptual overview

#### 1.1.1 Patterns are sets of states

Let `α` be the type of concrete states. A pattern `p` is interpreted as a set
of states:

```text
⟦p⟧ = { state : α | state satisfies p }
```

The class `framework.AtPattern α P` assigns this meaning to an atomic pattern
representation `P`:

```lean
class AtPattern (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop
```

Two instances create the user-facing closure representation.

A state value denotes the singleton containing that value:

```lean
instance [State α] : AtPattern α α where
  semantics pattern state := pattern = state
```

A function closure existentially binds its argument:

```lean
instance [State α] [AtPattern α P] : AtPattern α (A → P) where
  semantics pattern state :=
    ∃ argument, AtPattern.semantics (pattern argument) state
```

Therefore

```lean
fun x y : Conf => Conf.f x y
```

means all `Conf` states of the form `Conf.f x y`. Nested Lean lambdas become
nested semantic existential quantifiers. The logical variables `x` and `y`
are not values stored inside `Conf`.

A constrained atomic pattern returns `PatternBody α`:

```lean
structure PatternBody (α : Type u) where
  term : α
  requires : Prop := True
```

Its semantics is:

```text
term = state ∧ requires
```

Thus the same closure binds variables shared by the term and its condition.
For example:

```lean
fun n : Nat => {
  term := pair (atom 0) (atom n)
  requires := 0 < n
}
```

denotes exactly the pairs whose second payload is positive.

`framework.Pattern` extends atomic patterns with finite disjunction.
`Disjunction P Q` permits its two branches to have different Lean
representations, and `EmptyPattern α` denotes the empty set.

#### 1.1.2 Unifiability is semantic intersection

The framework defines:

```lean
def Unifiable (p : P) (q : Q) : Prop :=
  ∃ state,
    AtPattern.semantics p state ∧
    AtPattern.semantics q state

infix:50 " ⋈ " => Unifiable
```

Mathematically:

```text
p ⋈ q    iff    ⟦p⟧ ∩ ⟦q⟧ is nonempty.
```

This is deliberately a semantic proposition, not a Boolean invocation of a
solver. A hypothesis `h : p ⋈ q` already contains:

1. a common state;
2. witnesses for every binder in `p`;
3. witnesses for every binder in `q`; and
4. equalities showing that both instantiated patterns denote the common
   state.

The `unify` tactic analyzes those witnesses and equalities. It does not add a
new axiom asserting that the patterns are unifiable.

#### 1.1.3 An MGU is exposed by factorization

For a free first-order equation, a most general unifier `σ` has the usual
factorization property: every concrete unifier `θ` is an instance of `σ`.
There is some residual substitution `δ` such that:

```text
θ = δ after σ.
```

In the tactic interface, the parameters of `δ` are called **basis
variables**. Suppose the original closure arguments, in left-then-right order,
are:

```text
x1, x2, y1
```

and the MGU is:

```text
x1 ↦ f(u1, c)
x2 ↦ c
y1 ↦ u1.
```

The certified proposition exposed by the tactic is conceptually:

```text
∃ u1,
  x1 = f(u1, c) ∧
  x2 = c ∧
  y1 = u1.
```

The basis value `u1` is not an object term and does not require a `Conf.var`
constructor. It is an ordinary Lean local of type `Conf`.

#### 1.1.4 Multiple MGUs are a disjunction of factorizations

Free unification is unitary: a solvable problem has one MGU up to renaming.
Other equational axioms can produce a finite complete set of MGUs.

The common logical result is therefore:

```text
factorization₁ ∨ factorization₂ ∨ ... ∨ factorizationₙ.
```

The three important cases are:

- zero alternatives: the unifiability hypothesis implies `False`;
- one alternative: one factorization is opened in the current goal; and
- several alternatives: the proof is split into one goal per factorization.

This is why the free solver already returns a solution **set**, even though it
can contain at most one element. The same output interface can later carry C,
AC, ACU, or external-oracle results.

#### 1.1.5 Narrowing is unification followed by substitution

A constrained rewrite rule is also a closure:

```lean
structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  requires : Prop := True
```

The closure binds variables shared by `lhs`, `rhs`, and `requires`.

For one-step narrowing of a rule `r` against a source pattern `p`:

1. unify `r.lhs` with `p.term`;
2. for every MGU, substitute it into `r.rhs`;
3. conjoin the instantiated source and rule conditions; and
4. disjoin all resulting constrained successors.

The union of those successors is called `post`. Its intended semantics is the
exact one-step image:

```text
r ⊢ p ↝ post
```

which abbreviates `NarrowsTo r p post` and states:

```text
⟦post⟧ = postImage(r, p).
```

Because this is equality rather than inclusion, a certified `post` is
semantically the strongest, most precise one-step result. Individual
successors correspond to individual MGU branches; `post` is their
disjunction.

The reachability-style judgment

```text
r ⊢ p ↪ q
```

means every one-step result of `r` from `p` is contained in `q`. The proof is
decomposed into exact narrowing followed by subsumption:

```text
there exists post such that
  r ⊢ p ↝ post
and
  post ⊑ q.
```

This decomposition is embodied by `mapsInto_via_narrowing`.

### 1.2 Two running examples

The rest of the document repeatedly returns to these examples.

#### Running example F: one free MGU

The model contains no logical-variable constructor:

```lean
inductive Conf where
  | c : Conf
  | f : Conf → Conf → Conf
```

The two patterns are ordinary Lean functions:

```lean
def pat1 (x1 x2 : Conf) : Conf := f x1 x2
def pat2 (y1 : Conf) : Conf := f (f y1 c) c
```

Their equation is:

```text
f(x1, x2) = f(f(y1, c), c).
```

The MGU is:

```text
x1 ↦ f(u1, c)
x2 ↦ c
y1 ↦ u1.
```

The public proof is:

```lean
example (h : pat1 ⋈ pat2) : True := by
  unify h
  guard_hyp u1 : Conf
  guard_hyp h1 : x1 = f u1 c
  guard_hyp h2 : x2 = c
  guard_hyp h3 : y1 = u1
  exact True.intro
```

The `guard_hyp` lines are regression checks, not obligations imposed by the
tactic. A user normally continues reasoning with `u1`, `h1`, `h2`, and `h3`.

#### Running example N: narrowing and subsumption

The source and target are constrained patterns:

```lean
def source (n : Nat) : PatternBody Conf where
  term := pair (atom 0) (atom n)
  requires := 0 < n

def target (payload : Nat) : PatternBody Conf where
  term := pair (atom payload) (atom (payload + 1))
  requires := 0 < payload
```

The rule is:

```lean
def advance (payload next : Nat) : RuleBody Conf where
  lhs := pair (atom 0) (atom payload)
  rhs := pair (atom payload) (atom next)
  requires := next = payload + 1
```

Unifying `advance.lhs` with `source.term` gives:

```text
payload ↦ u1
next    ↦ u2
n       ↦ u1.
```

Substituting into the RHS and both constraints gives the generated successor:

```lean
fun u1 u2 : Nat => {
  term := pair (atom u1) (atom u2)
  requires := 0 < u1 ∧ u2 = u1 + 1
}
```

The complete user proof is:

```lean
example : advance ⊢ source ↪ target := by
  apply mapsInto_via_narrowing
  narrow advance against source
  subsume
```

The three lines intentionally expose the three mathematical phases:

1. `apply` changes the goal to narrowing plus subsumption through an unknown
   post;
2. `narrow` computes the post and proves it is the exact one-step image; and
3. `subsume` proves that the generated post is included in `target`.

### 1.3 Architectural overview

The implementation is one Lean file for prototyping, but its namespaces are
intended as future file boundaries.

```text
Public judgments and tactics
│
├── framework
│   ├── semantic domains: State, AtPattern, Pattern, AtRule
│   ├── judgments: Unifiable, NarrowsTo, Subsumes, mapsInto
│   └── equational registration: Axiom, Symbol, EqModule
│
├── Unification
│   ├── Tactic                     top-level orchestrator
│   │   ├── Problem                extract a first-order equation
│   │   ├── PresentationElaboration choose free or C from EqModule
│   │   ├── Free or C              compute and certify alternatives
│   │   └── Presentation           expose basis variables/equations
│   └── Certificate                backend-neutral interchange format
│
└── Narrowing
    ├── Problem                    form rule.lhs = source.term
    ├── Backend                    obtain Certificate.SolutionSet
    ├── Materialization            substitute MGUs into RHS/constraints
    ├── Certification              prove exact NarrowsTo semantics
    └── Subsumption                prove the residual post ⊑ target goal
```

The principal dependency rule is:

> Outer orchestration modules may depend on inner data interfaces, but
> backend-specific mutable metavariables and evidence must not escape their
> backend.

The most important boundary is `Unification.Certificate`:

```text
Problem.Input
     │
     ▼
backend-private computation
     │
     ▼
Certificate.SolutionSet / ProvenSolutionSet
     │
     ├── Presentation: user proof context
     └── Narrowing.Materialization: generated post
```

This boundary is what makes later replacement by an AC solver or an external
oracle possible without redesigning the user interface.

---

## 2. Public semantic and proof interfaces

This section starts at the outside of the tree: what users state and what the
tactics promise.

### 2.1 The framework layer

#### 2.1.1 State and atomic-pattern interfaces

User models opt into the framework with an empty proposition-valued instance:

```lean
instance : framework.State Conf := ⟨⟩
```

`State` carries no syntax and imposes no variable representation. It only
marks the intended semantic state type for typeclass inference.

`AtPattern` supplies atomic semantics. `Pattern` supplies semantics closed
under disjunction. This split is why narrowing can return a heterogeneous
disjunction of successor closures while individual user patterns remain simple
lambda closures.

The representations form this semantic tree:

```text
AtPattern
├── model value α                    singleton
├── α × Prop                        equality plus condition
├── PatternBody α                   term plus condition
└── A → P                           existential closure

Pattern
├── every AtPattern                 atomic branch
└── Disjunction P Q                 semantic union

EmptyPattern α                      false atomic branch
```

#### 2.1.2 Rule interface

`AtRule α R` interprets a rule representation as a relation between states:

```lean
class AtRule (α : outParam (Type u)) [State α] (R : Type v) where
  semantics : R → α → α → Prop
```

`RuleBody α` means:

```text
lhs = before ∧ rhs = after ∧ requires.
```

As with patterns, the function instance interprets rule closures
existentially. One lambda therefore shares variables across all three fields.

#### 2.1.3 Unification judgments

The two forms are:

```lean
p ⋈ q
p ⋈[M] q
```

The first uses free unification by default. The second carries an `EqModule`
used by automation to select an equational backend.

Logically, `UnifiableIn M p q` currently reduces to `Unifiable p q`:

```lean
def UnifiableIn (_presentation : EqModule) (left : P) (right : Q) : Prop :=
  Unifiable left right
```

Thus `EqModule` does not alter denotational semantics or add an untrusted
proposition. It is an explicit automation parameter attached to the theorem
statement.

The public tactics are:

```lean
unify h                  -- free backend
c_unify h                -- explicit C backend
unify h in M             -- dispatch according to M
```

All successful forms expose the same basis-and-equations interface.

#### 2.1.4 Narrowing judgments

The semantic definitions are:

```lean
postImage rule source after
Subsumes source target
NarrowsTo rule source post
mapsInto rule source target
```

The corresponding notation is:

```text
rule ⊢ source ↝ post      exact one-step image
post ⊑ target             semantic inclusion
rule ⊢ source ↪ target    all one-step results land in target
```

The theorem `mapsInto_of_narrowsTo_of_subsumes` composes an already chosen
post. The theorem used by the tactic proof script is
`mapsInto_via_narrowing`, which existentially packages:

- the Lean type `Post` of the generated representation;
- its `Pattern` instance;
- the generated value `post`;
- the proof `rule ⊢ source ↝ post`; and
- the remaining proof `post ⊑ target`.

The type itself must be existential because a future multi-MGU post may be a
nested heterogeneous `Disjunction` whose precise Lean type is known only
after solving.

### 2.2 Stable user-visible output of `unify`

The output order is part of the public interface:

1. basis locals named `u1`, `u2`, ...;
2. one equation for every original pattern argument;
3. arguments ordered left pattern first, then right pattern; and
4. equations named `h1`, `h2`, ....

For running example F, the original arguments are `[x1, x2, y1]`, so the
output is:

```text
u1 : Conf
h1 : x1 = f u1 c
h2 : x2 = c
h3 : y1 = u1
```

Neither Lean's internal metavariable names nor an external solver's textual
binding order determines this interface.

If a solver returns several alternatives, each goal independently receives
locals named from `u1` and equations named from `h1`. If it returns none, the
original goal is closed using a certified contradiction.

---

## 3. Top-down unification workflow

This section follows `unify h` from the outer tactic call down to the solver
and back up to the proof context.

### 3.1 Root: syntax and `Unification.Tactic`

The syntax elaborators are intentionally thin:

```lean
elab "unify " h:ident : tactic =>
  Unification.Tactic.run h.raw h

elab "c_unify " h:ident : tactic =>
  Unification.Tactic.runC h.raw h

elab "unify " h:ident " in " presentation:term : tactic =>
  Unification.Tactic.runIn h.raw h presentation
```

`run`, `runC`, and `runIn` all reach the private higher-order function
`runWith`.

Its abstract backend interface is:

```text
solve
  : Problem.Input → MetaM Output

certify
  : Output
  → actual arguments
  → actual identifiers
  → irrelevant semantic hypotheses
  → TacticM Certificate.ProvenSolutionSet
```

`runWith` executes the complete outer workflow:

```text
1. Read p and q from the type of h.
2. Build Problem.Input using fresh symbolic metavariables.
3. Call the selected backend's solve function.
4. Open the semantic witnesses stored in h.
5. Derive the concrete equality between instantiated pattern terms.
6. Ask the backend to certify its computed result from that equality.
7. Pass the proof to Presentation.expose.
8. Clear semantic bookkeeping, leaving only public locals and equations.
```

#### Boundary of `Unification.Tactic`

- **Receives:** a hypothesis identifier and a pair of backend functions.
- **Returns:** modified Lean goals containing only public unifier data.
- **Depends on:** `Problem`, one backend, `Certificate`, and `Presentation`.
- **Does not know:** the algorithm used to find substitutions.

This is the main replacement seam for a future solver.

### 3.2 Child: `Unification.Problem`

#### 3.2.1 Saturating closures

`Problem.SaturatedPattern` stores:

```lean
structure SaturatedPattern where
  application : Expr
  arguments : Array Expr
  argumentNames : Array Name
```

For running example F, `saturatePattern pat1` conceptually produces:

```text
application   = f ?x1 ?x2
arguments     = [?x1, ?x2]
argumentNames = [x1, x2]
```

and `saturatePattern pat2` produces:

```text
application   = f (f ?y1 c) c
arguments     = [?y1]
argumentNames = [y1].
```

The metavariables are temporary computational variables owned by Lean's meta
state. They are not yet the public basis variables.

`saturatePattern` accepts explicit closure binders. Implicit or instance
binders are currently rejected so that the correspondence between source
arguments and public equations is unambiguous.

#### 3.2.2 Reading the hypothesis type

`Problem.ofUnifiableType` recognizes either:

```text
Unifiable p q
UnifiableIn M p q.
```

It returns:

```lean
structure Input where
  presentation? : Option Expr
  lhs : SaturatedPattern
  rhs : SaturatedPattern
```

The optional presentation is metadata for dispatch. Both backends receive the
same saturated left and right equation.

#### Boundary of `Unification.Problem`

- **Receives:** the Lean expression representing the type of `h`.
- **Returns:** a backend-neutral first-order equation plus original argument
  order and names.
- **Depends on:** only the semantic shape of `Unifiable`/`UnifiableIn` and
  Lean elaboration.
- **Does not know:** free, C, AC, narrowing, or the eventual proof goal.

### 3.3 Child: exposing the semantic equality

Computation uses the fresh metavariables in `Problem.Input`, but certification
must concern the actual witnesses contained in `h`.

`Tactic.exposeSemantics` destructs `h` in this order:

```text
common state
├── witnesses and semantics proof for the left closure
└── witnesses and semantics proof for the right closure
```

It then composes the two equalities through the common state:

```text
leftTerm = commonState
rightTerm = commonState
--------------------------------
leftTerm = rightTerm.
```

For running example F this becomes the kernel-checked equality:

```text
f x1 x2 = f (f y1 c) c.
```

This equality, not the mutable assignments produced during solving, is the
foundation of the final certificate.

### 3.4 Child: `Unification.Certificate`

`Certificate` is the shared language between solvers and consumers.

#### 3.4.1 One alternative

```lean
structure Alternative where
  basisTypes : Array Expr
  images : Array Expr
```

Every `image` is a lambda over all basis variables. Running example F is
represented conceptually as:

```text
basisTypes = [Conf]

images = [
  fun u1 => f u1 c,    -- image of x1
  fun u1 => c,         -- image of x2
  fun u1 => u1         -- image of y1
].
```

The images are ordered by `Problem.symbolicArguments`, not by solver output
order.

Crucially, these expressions contain no backend-owned metavariables. Residual
freedom has already been lambda-abstracted into the explicit basis.

#### 3.4.2 A solution set

```lean
structure SolutionSet where
  alternatives : Array Alternative
```

This is computational data. It can be consumed by narrowing before a
user-facing factorization proof is opened.

#### 3.4.3 Proven results

`ProvenAlternative` pairs one alternative with its factorization proposition
and proof. `ProvenSolutionSet` contains:

```lean
structure ProvenSolutionSet where
  solutionSet : SolutionSet
  branchPropositions : Array Expr
  proposition : Expr
  proof : Expr
```

`Certificate.factorizationType` turns images into:

```text
∃ basis,
  originalArg₁ = image₁(basis) ∧
  ... ∧
  originalArgₙ = imageₙ(basis) ∧
  True.
```

The trailing `True` makes construction uniform even for zero original
arguments. `Presentation` removes it before returning control to the user.

`Certificate.solutionSetType` disjoins all branch propositions. An empty
array becomes `False`.

#### 3.4.4 Exact logical strength of the current certificate

The proof inside `ProvenSolutionSet` is constructed in the local context
obtained by opening `h : p ⋈ q`. It proves that the **actual witnesses carried
by `h`** factor through at least one returned alternative. This is the
coverage/completeness fact required by the user-facing tactic.

It is not yet a standalone, first-class theorem saying, independently of `h`,
that every returned lambda substitution unifies the two symbolic terms for
all basis values. The current free and C backends compute such substitutions
and replay enough reasoning to establish the factorization disjunction, but
the certificate data type records coverage rather than a separate soundness
theorem for each branch.

This distinction does not compromise Lean's logical soundness: every fact
placed in the user's context still has a kernel-checked proof. It does matter
for backend validation and usability. A future external-oracle boundary should
either enrich each alternative with an independent unifier proof or validate
that property during certificate replay, in addition to proving coverage.

#### Boundary of `Unification.Certificate`

- **Receives:** basis types and closed substitution images from any solver.
- **Returns:** a canonical factorization formula or disjunction.
- **Depends on:** only original argument order and ordinary Lean equality,
  existential, conjunction, and disjunction.
- **Does not know:** how alternatives were computed, what axioms were used,
  or whether the consumer is `Presentation` or `Narrowing`.

### 3.5 Leaf backend: `Unification.Free`

#### 3.5.1 Computation uses Lean's native unifier

The free algorithm is **not** implemented from scratch. `Free.solve` invokes:

```lean
isDefEq problem.lhs.application problem.rhs.application
```

For first-order constructor terms, Lean's native definitional-equality
unifier performs decomposition, assignment, and the occurs check.

For running example F it assigns the temporary metavariables so that:

```text
?x1 = f ?y1 c
?x2 = c
```

with `?y1` residual. The backend then:

1. instantiates every original symbolic argument;
2. collects distinct residual metavariables;
3. checks that every residual came from an original pattern argument;
4. records the residual's type as a basis type; and
5. replaces residuals by fresh locals and lambda-abstracts them.

The result is the `Certificate.Alternative` shown above.

#### 3.5.2 Backend-private evidence

`Free.Candidate` adds `basisWitnesses` to the common alternative:

```lean
structure Candidate where
  alternative : Certificate.Alternative
  basisWitnesses : Array Nat
```

These indices say which actual existential witness can instantiate each
residual basis while constructing the proof. They are a private convenience
for free certification and do not cross the `Certificate` boundary.

#### 3.5.3 Success certification

`Free.certifySuccess` constructs the factorization proposition dictated by
the candidate, introduces actual witnesses for its basis variables, and asks
Lean to prove the resulting equations with `simp_all`.

This separation matters:

- `isDefEq` proposes the substitution;
- `Certificate.factorizationType` states its public meaning; and
- the semantic equality extracted from `h` proves that meaning.

The tactic therefore does not trust an uninspected mutable metavariable state
as a proof.

#### 3.5.4 Failure certification

If `isDefEq` reports failure, `Free.certify` must prove that `h` is
contradictory.

There are two cases in the current fragment:

- direct constructor clashes are discharged by `simp_all`; and
- occurs-check cycles are mapped through `SizeOf.sizeOf`, reduced to
  impossible natural-number equations, and checked with `omega`.

For example:

```lean
(fun x : Conf => f x x) ⋈
(fun y : Conf => f (f y c) y)
```

would imply `y = f y c`, contradicting finiteness of the inductive `Conf`
term. The tactic produces a proof of `False` from `h` and can consequently
close any target, not only a target already written as `False`.

#### Boundary of `Unification.Free`

- **Receives:** `Problem.Input`.
- **Computes:** zero or one candidate using native unification.
- **Certifies:** a complete zero-or-one `ProvenSolutionSet`.
- **Exports:** only closed basis lambdas and kernel-checked factorization
  proofs.
- **Assumes:** the supported free constructor fragment described later.

### 3.6 Leaf backend: `Unification.C`

The C backend demonstrates that the certificate and presentation interfaces
can support several alternatives without changing user proofs.

#### 3.6.1 Why commutativity needs more than `f_comm`

The current backend models a symbol that is **free modulo commutativity**.
Commutativity alone is not enough to characterize equality: a constant binary
operation is commutative but has many equations unrelated to swapping.

The temporary backend contract is:

```lean
class C.Operator (op : α → α → α) extends Std.Commutative op where
  eq_iff (a b c d : α) :
    op a b = op c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)
```

`eq_iff` is the free-C decomposition principle used to certify that the direct
and swapped cases are complete.

#### 3.6.2 Computing orientations

`C.solve` recursively enumerates every term obtained by swapping children at
registered C nodes on the right-hand side. It invokes `Free.solve` independently
for each orientation and removes duplicate alternatives.

Each free attempt runs under `withoutModifyingState`, because native
unification assigns temporary metavariables and every orientation must start
from the same original problem.

Consider:

```lean
pairLeft  x y := f x y
pairRight a b := f a b
```

modulo `f x y = f y x`. There are two MGU branches:

```text
direct:                       swapped:
x ↦ u1                        x ↦ u1
y ↦ u2                        y ↦ u2
a ↦ u1                        a ↦ u2
b ↦ u2                        b ↦ u1
```

The common `SolutionSet` holds two `Alternative` values.

#### 3.6.3 C certification and presentation

`C.certify` builds the disjunction of both factorization formulas and proves
it using `C.Operator.eq_iff`, `simp_all`, and `grind`.

`Presentation.expose` then splits the disjunction, giving the user two goals:

```lean
example (h : pairLeft ⋈[Module1] pairRight) : True := by
  unify h in Module1
  · -- direct branch with u1, u2, h1, ..., h4
    exact True.intro
  · -- swapped branch with u1, u2, h1, ..., h4
    exact True.intro
```

The public shape is identical to free unification; only the number and
contents of branches differ.

### 3.7 Return path: `Unification.Presentation`

`Presentation.expose` is the final axiom-independent layer.

For each alternative it:

1. adds the certified factorization proof to the goal;
2. opens each existential basis variable and names it `u1`, `u2`, ...;
3. opens each conjunctive equation and names it `h1`, `h2`, ...;
4. removes the trailing implementation-only `True`; and
5. preserves original argument order.

For multiple alternatives, `exposeAlternativesAt` recursively cases on the
certified disjunction. For an empty result, `expose` notes the certified
`False` proof and closes the original goal by contradiction.

#### Boundary of `Unification.Presentation`

- **Receives:** `Certificate.ProvenSolutionSet`.
- **Returns:** zero, one, or several ordinary Lean goals.
- **Depends on:** only the certificate's logical structure.
- **Does not know:** whether the result came from native free unification, C
  orientation enumeration, or a future external oracle.

---

## 4. Equational modules and backend dispatch

### 4.1 Uniform symbol declarations

`framework.Symbol` packages an operation existentially with its Lean type:

```lean
structure Symbol where
  {operationType : Type u}
  operation : operationType
  axioms : List (Axiom operation) := []
```

Its uniform constructor is:

```lean
Symbol.declare operation axioms
```

No arity is special at the symbol-registration layer. A single module can
contain:

```lean
def MixedArityFree : framework.EqModule where
  symbols := [
    framework.Symbol.declare zeroSymbol,    -- Nat
    framework.Symbol.declare increment,     -- Nat → Nat
    framework.Symbol.declare firstOfThree,  -- Nat → Nat → Nat → Nat
    framework.Symbol.declare select         -- Nat → Bool → Nat
  ]
```

Lean infers each complete signature from the operation. The list is
heterogeneous because every `Symbol` existentially packages its own
`operationType`.

### 4.2 Axioms are dependent on their operation

`framework.Axiom` is indexed by the exact operation:

```lean
inductive Axiom : {operationType : Type u} →
    (operation : operationType) → Type (u + 1) where
  | commutative ... : Axiom operation
  | associative ... : Axiom operation
```

The binary restriction belongs to these mathematical schemas, not to
`Symbol`. For example:

```lean
framework.Symbol.declare f [.commutative f_comm]
```

is accepted because `f` is binary and `f_comm` proves the required law about
that exact `f`. A proof about another operation cannot be inserted into this
list: Lean rejects it by dependent type checking.

Known Lean operations can reuse existing theorems:

```lean
def NatAC : framework.EqModule where
  symbols := [framework.Symbol.declare Nat.add [
    .associative Nat.add_assoc,
    .commutative Nat.add_comm
  ]]
```

This declaration elaborates, but the current tactic deliberately reports that
the AC backend is not implemented if asked to use it.

### 4.3 `EqModule`

```lean
structure EqModule where
  symbols : List Symbol := []
```

`EqModule` is framework data, not a member of `Unification`. Unification,
narrowing, and future reachability procedures can all interpret the same
equational component. A future full rewrite module can own an `EqModule`
together with rules and other model declarations.

An empty module selects free unification:

```lean
def FreePresentation : framework.EqModule := {}
```

The explicit free proof has the same output as bare `unify`:

```lean
example (h : pat1 ⋈[FreePresentation] pat2) : True := by
  unify h in FreePresentation
  ...
```

### 4.4 `Unification.PresentationElaboration`

This namespace interprets `EqModule` only far enough to choose the current
backend:

```text
no registered axioms       → Free
at least one commutative   → C
associative only           → explicit unsupported error
associative + commutative  → explicit AC-unsupported error
```

The dispatcher scans arbitrary-arity symbols uniformly. Only encountering an
axiom constructor affects backend choice.

`Tactic.runIn` also checks that the module written after `in` is definitionally
the same module appearing in `h : p ⋈[M] q`. This prevents accidentally
proving a module-indexed hypothesis with a different presentation.

### 4.5 Current module/C duplication

The module interface is not yet the sole source of C information:

- `EqModule` and `.commutative f_comm` select the C backend;
- `C.Operator f` lets the C solver recognize `f` in a term; and
- `C.Operator.eq_iff` certifies free-C decomposition and completeness.

Consequently the current example registers both:

```lean
instance : Unification.C.Operator f where
  comm := f_comm
  eq_iff := f_eq_iff

noncomputable def Module1 : framework.EqModule where
  symbols := [framework.Symbol.declare f [.commutative f_comm]]
```

This duplication is a known prototype limitation, not the intended final
contract. A future implementation should reify symbol declarations from the
selected module and derive backend recognition and certificate replay from
module-owned information.

In particular, C-operation discovery is currently global typeclass synthesis,
not a lookup restricted to the selected `EqModule`. Once any commutative axiom
causes module dispatch to choose C, the C backend recognizes every operation
having a visible `C.Operator` instance. The examples keep those registrations
aligned, but the framework does not yet enforce that alignment.

Another current simplification is that dispatch chooses one backend for the
whole module. A general Ax-unifier will need per-symbol axioms inside one
reified problem rather than the present coarse `free`/`c` choice.

---

## 5. Top-down narrowing workflow

Narrowing is a separate outer client. `unify` remains independently usable;
the rule layer does not own or replace `Unification.Certificate`.

### 5.1 Root: the user proof decomposition

For running example N:

```lean
example : advance ⊢ source ↪ target := by
  apply mapsInto_via_narrowing
  narrow advance against source
  subsume
```

After `apply mapsInto_via_narrowing`, the proof goal explicitly asks for:

```text
∃ Post, ∃ postPattern : Pattern Conf Post, ∃ post : Post,
  advance ⊢ source ↝ post ∧
  post ⊑ target.
```

The user does not name or construct `post`. Its representation depends on the
number and types of MGU alternatives, so `narrow` computes and binds it.

### 5.2 Child: `Narrowing.Problem`

`Narrowing.Problem` reuses `Unification.Problem.saturatePattern` for both rule
and source closures.

It projects:

```text
rule closure   → lhs, rhs, rule requires
source closure → term, source requires
```

and creates the structural unification problem:

```text
rule.lhs = source.term.
```

The ordering of symbolic arguments is:

```text
all rule binders, then all source binders.
```

For running example N this is `[payload, next, n]`.

#### Boundary of `Narrowing.Problem`

- **Receives:** one closure returning `RuleBody` and one returning
  `PatternBody`.
- **Returns:** projected rule/source data plus `Unification.Problem.Input`.
- **Depends on:** the common closure-saturation frontend.
- **Does not know:** how MGUs will be computed or how the post is represented.

### 5.3 Child: `Narrowing.Backend`

The current bridge calls:

```lean
Unification.Free.solve problem.unification
```

and immediately erases `Free.Candidate.basisWitnesses`, retaining only:

```lean
Unification.Certificate.SolutionSet.
```

This demonstrates the intended dependency: post construction needs basis
types and substitution images, not free-backend proof bookkeeping.

The current `narrow` tactic is free-only. It does not yet accept `in M` or use
the C dispatcher. Generalizing this small `Narrowing.Backend` bridge is one of
the clear steps toward Ax-narrowing.

### 5.4 Child: `Narrowing.Materialization`

For each `Certificate.Alternative`, `Materialization.successor`:

1. creates locals with the recorded `basisTypes`;
2. instantiates every substitution image at those basis locals;
3. divides images into rule arguments and source arguments;
4. applies substituted rule arguments to the rule closure;
5. reads the instantiated RHS and rule condition;
6. applies substituted source arguments to the source closure;
7. reads the instantiated source condition; and
8. constructs a closure returning:

```lean
PatternBody.mk substitutedRhs
  (substitutedSourceCondition ∧ substitutedRuleCondition).
```

For running example N, this is exactly:

```lean
fun u1 u2 => {
  term := pair (atom u1) (atom u2)
  requires := 0 < u1 ∧ u2 = u1 + 1
}
```

`Materialization.post` handles the complete solution set:

```text
zero alternatives → EmptyPattern
one alternative   → one successor closure
many alternatives → heterogeneous disjunction of successors.
```

The returned `Materialization.Post` existentially packages its computed Lean
type and value at the meta level.

#### Constraints and filtering

The structural backend currently computes MGUs before considering
constraints. Constraints are then substituted into every successor. A branch
whose combined condition is inconsistent denotes the empty set and can be
eliminated during narrowing certification or subsumption.

For example, `constrainedOut` structurally unifies with `source`, but its
conditions become:

```text
0 < u1 ∧ u1 = 0,
```

so the branch is semantically empty.

This is logical filtering, but not yet an optimized solver-level filter. If a
future AC problem returns thousands of MGUs, the backend/materialization
boundary can be extended to simplify constraints before retaining every
alternative.

### 5.5 Child: `Narrowing.Certification`

Materialization creates a candidate post; it does not by itself establish
that the post is complete or sound.

`Certification.prove` creates and proves:

```text
NarrowsTo rule source post.
```

It unfolds the relevant rule and source closure definitions, expands the
semantic definitions, and currently uses `simp` plus `grind` to replay free
constructor reasoning.

This certification path is separate from `Free.certify`: narrowing consumes
raw `SolutionSet` data to construct a new semantic object, then proves the
meaning of that new object directly.

For future AC narrowing, `Narrowing.Certification` must either replay the
equational certificate or consume richer checked evidence from the backend.

### 5.6 Return path: `Narrowing.Tactic`

`Narrowing.Tactic.run` expects exactly the existential goal created by:

```lean
apply mapsInto_via_narrowing
```

It then:

1. elaborates the rule and source terms;
2. builds the narrowing problem;
3. computes the solution set;
4. materializes `post`;
5. defines a local named `post` without user input;
6. proves a local named `narrowing : rule ⊢ source ↝ post`; and
7. fills the existential `Post`, its inferred `Pattern` instance, `post`, and
   `narrowing` proof.

Only this residual goal remains:

```text
post ⊑ target.
```

### 5.7 Leaf: `Narrowing.Subsumption`

`subsume` recognizes a goal of the form `source ⊑ target`, unfolds the
definitions directly supplying both pattern closures, expands semantic
definitions, and invokes `simp` and `grind`.

It is intentionally simple. The semantic `Subsumes` interface is stable even
if future work replaces this prototype automation with an SMT solver, custom
constraint procedure, or user-guided proof.

#### Boundary of narrowing as a whole

- **Receives:** a rule closure, source closure, and an existential
  narrowing/subsumption proof goal.
- **Consumes:** backend-neutral `Certificate.SolutionSet` alternatives.
- **Produces:** a generated `Pattern` post plus a proof of exact semantics.
- **Leaves:** only semantic subsumption to the user or `subsume` tactic.
- **Does not change:** the standalone `unify` tactic or its public interface.

---

## 6. Dependency and interface reference

### 6.1 Unification dependency tree

```text
Unification.Tactic.runWith
├── Unification.Problem.ofUnifiableType
│   └── Unification.Problem.saturatePattern
├── backend.solve
│   ├── Unification.Free.solve
│   └── Unification.C.solve
│       └── Unification.Free.solve
├── Tactic.exposeSemantics
├── backend.certify
│   ├── Unification.Free.certify
│   └── Unification.C.certify
│       └── C.Operator.eq_iff
└── Unification.Presentation.expose
    └── Unification.Certificate factorization structure
```

### 6.2 Narrowing dependency tree

```text
mapsInto_via_narrowing
└── narrow rule against source
    ├── Narrowing.Problem.ofTerms
    │   └── Unification.Problem.saturatePattern
    ├── Narrowing.Backend.solve
    │   └── Unification.Free.solve
    ├── Narrowing.Materialization.post
    │   └── Unification.Certificate.Alternative
    ├── Narrowing.Certification.prove
    └── residual post ⊑ target
        └── subsume
```

### 6.3 Interface table

| Component | Input | Output | Replaceable without changing users? |
|---|---|---|---|
| `framework.AtPattern` | user representation | set-of-states semantics | yes, per representation |
| `Unification.Problem` | `p ⋈ q` hypothesis type | saturated equation | normally stable |
| `PresentationElaboration` | `EqModule` | backend tag | yes |
| `Free.solve` | saturated equation | private free candidates | yes |
| `C.solve` | saturated equation | private C candidates | yes |
| `Certificate` | basis and images | canonical solution-set language | intended stable boundary |
| backend `certify` | candidates plus semantic witnesses | proven solution set | axiom-specific and replaceable |
| `Presentation.expose` | proven solution set | user locals/goals | intended stable public interface |
| `Narrowing.Backend` | LHS/source equation | raw solution set | yes; current Ax extension point |
| `Materialization` | solution set plus rule/source | constrained post | intended axiom-neutral |
| narrowing certification | candidate post | exact-image proof | axiom-specific and replaceable |
| `Subsumption` | `post ⊑ target` | proof | yes |

### 6.4 What an AC or external backend must provide

The stable computational target is an array of
`Certificate.Alternative`s. For each MGU branch, a backend must provide:

1. the types of residual basis variables;
2. one closed lambda image for every original argument;
3. images ordered left arguments then right arguments; and
4. no solver-owned metavariables.

For an external result such as:

```text
X  --> f(%1, %2)
Y  --> %2
```

the Lean adapter would construct something like:

```text
basisTypes = [Term, Term]
images = [
  fun u1 u2 => f u1 u2,
  fun u1 u2 => u2
].
```

It must then certify both:

- **soundness:** every returned substitution is an actual Ax-unifier; and
- **completeness/factorization:** every semantic witness represented by `h`
  factors through at least one returned alternative.

The current `ProvenSolutionSet` directly records the second property relative
to `h`; an external-oracle integration should strengthen or supplement it to
record the first property explicitly as well.

An external oracle may compute candidates, but Lean should replay a
certificate or otherwise construct the final `ProvenSolutionSet`. Once that
object exists, `Presentation.expose` and the public proof scripts need no
Ax-specific changes.

For narrowing, the backend must additionally allow
`Narrowing.Materialization` to substitute alternatives into RHS terms and
conditions, and narrowing certification must prove that their disjunction is
the exact semantic post image.

---

## 7. Trust model

The prototype distinguishes computation from proof.

### 7.1 Trusted foundation

Ultimately trusted:

- Lean's kernel;
- the semantic definitions in `framework`; and
- explicit user axioms such as `f_comm` and `f_eq_iff`, when the example
  chooses to assume them.

### 7.2 Untrusted or rechecked computation

Used to propose results but not accepted as final proof merely by execution:

- assignments made by `isDefEq`;
- enumeration and deduplication of C orientations;
- construction of substitution-image expressions; and
- materialization of successor closures.

Each path ends in proof construction:

```text
free candidate       → factorization proof
free failure         → False proof
C alternatives       → disjunction-of-factorizations proof
materialized post    → NarrowsTo equivalence proof
subsumption tactic   → Subsumes proof
```

If certification fails, the tactic reports an error instead of exposing an
uncertified result.

### 7.3 Role of Lean-native unification

Lean's native unifier is the computational engine for the free case. This is
an intentional implementation shortcut, not a logical shortcut:

- computation benefits from Lean's existing metavariable and occurs-check
  machinery;
- residual metavariables are abstracted before leaving `Free.solve`; and
- the result is reconstructed as an ordinary proposition proved from `h`.

---

## 8. Supported fragment and known limitations

### 8.1 Free unification

The prototype targets first-order constructor-style terms with:

- explicit closure binders;
- ordinary inductive constructors and reducible definitions;
- nondependent residual basis types;
- generated `SizeOf` support when occurs-check failure needs size reasoning;
  and
- constraints handled outside the structural solver.

It deliberately reports an error rather than pretending to support:

- higher-order unification;
- implicit or instance pattern binders;
- dependent basis types;
- native metavariables not traceable to original pattern arguments; or
- failures whose contradiction cannot be replayed by the present
  `simp_all`/`SizeOf`/`omega` procedure.

### 8.2 C unification

The C backend is a proof of extensibility, not a general equational unifier.
It currently requires:

- binary operations satisfying the strong free-C `Operator.eq_iff` law;
- a separate `C.Operator` instance for term recognition/certification;
- finite recursive orientation enumeration; and
- certificate replay by `simp_all [Operator.eq_iff]` and `grind`.

### 8.3 Equational modules

`EqModule` already supports:

- multiple symbols;
- different arities and argument sorts;
- operation-indexed axiom proofs; and
- free, associative, and commutative declarations at the data level.

Current dispatch does **not** yet support:

- a genuine mixed per-symbol Ax problem;
- A, AC, ACU, CU, or other algorithms;
- obtaining all C proof data solely from `EqModule`; or
- a full rewrite module containing rules and a distinguished state sort.

### 8.4 Narrowing

Current narrowing:

- calls only the free backend;
- computes structural MGUs before simplifying constraints;
- materializes zero, one, or many branches through the common result format;
- certifies exact posts using free constructor simplification; and
- uses a deliberately small `subsume` procedure.

The semantic architecture is already multi-branch, but the current bridge
does not yet invoke C or AC backends.

---

## 9. End-to-end traces

### 9.1 Running example F

```text
h : pat1 ⋈ pat2
│
├── Problem
│   ├── lhs = f ?x1 ?x2
│   ├── rhs = f (f ?y1 c) c
│   └── original order = [?x1, ?x2, ?y1]
│
├── Free.solve using isDefEq
│   ├── ?x1 := f ?y1 c
│   ├── ?x2 := c
│   └── residual basis = [?y1]
│
├── Certificate.Alternative
│   ├── basisTypes = [Conf]
│   └── images = [λu, f u c; λu, c; λu, u]
│
├── exposeSemantics h
│   └── equality = f x1 x2 = f (f y1 c) c
│
├── Free.certify
│   └── proof of ∃u1, x1 = f u1 c ∧ x2 = c ∧ y1 = u1 ∧ True
│
└── Presentation.expose
    ├── u1 : Conf
    ├── h1 : x1 = f u1 c
    ├── h2 : x2 = c
    └── h3 : y1 = u1
```

### 9.2 Running example N

```text
goal: advance ⊢ source ↪ target
│
├── apply mapsInto_via_narrowing
│   └── request an unknown exact post plus post ⊑ target
│
├── narrow advance against source
│   ├── Problem: advance.lhs = source.term
│   ├── Free.solve: payload ↦ u1, next ↦ u2, n ↦ u1
│   ├── Materialization.successor
│   │   ├── rhs = pair (atom u1) (atom u2)
│   │   └── condition = 0 < u1 ∧ u2 = u1 + 1
│   ├── bind generated local post
│   └── Certification.prove: advance ⊢ source ↝ post
│
└── subsume
    └── prove post ⊑ target by semantic simplification
```

---

## 10. Recommended reading order in the Lean file

For a code review or advisor discussion, the following order mirrors this
document and avoids beginning in low-level metaprogramming:

1. `framework.Unifiable`, `NarrowsTo`, `Subsumes`, and `mapsInto`;
2. the free and narrowing examples at the bottom of the file;
3. `Unification.Certificate` as the central modular interface;
4. `Unification.Tactic.runWith` as the outer workflow;
5. `Unification.Problem` and `Tactic.exposeSemantics`;
6. `Unification.Free.solve` and `Free.certify`;
7. `Unification.Presentation.expose`;
8. `framework.Axiom`, `Symbol`, `EqModule`, and
   `PresentationElaboration`;
9. `Unification.C` as the first multi-MGU extension; and
10. `Narrowing.Problem`, `Materialization`, `Certification`, and
    `Subsumption`.

The core architectural message is visible after steps 1–4:

```text
semantic proposition
    → backend-neutral problem
    → replaceable solver
    → certified solution set
    → stable user proof interface.
```

Narrowing reuses the same middle representation:

```text
rule/source closures
    → unification problem
    → solution set
    → substituted constrained successors
    → certified exact post
    → subsumption.
```

That is the organizing principle of the current prototype and the intended
foundation for later generalized constrained-pattern narrowing.
