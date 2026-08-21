# Free unification in Lean: architecture and tutorial

This document explains the prototype in `free-unification.lean`, concentrating
on the `free_unification.Unification` namespaces and the public tactic

```lean
unify h
```

The central design goal is slightly unusual. We want Lean itself to compute
free first-order unifiers, but we want the result to have the same shape that a
future AC or ACU unifier would use:

```text
basis values u1, ..., uk
one substitution equation for every original pattern argument
possibly several alternative unifiers
```

The object language therefore has no variable constructor. Users define an
ordinary inductive model such as `Conf`; basis variables are ordinary Lean
locals introduced only in the proof.

## 1. Semantic starting point

The framework marks a type as a state space:

```lean
class State (α : Type u) : Prop where
```

An `AtPattern α P` gives values of type `P` a semantics as sets of `α` states:

```lean
class AtPattern (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop
```

Two instances matter here. A state value denotes exactly itself:

```lean
instance [State α] : AtPattern α α where
  semantics pattern state := pattern = state
```

A Lean function is interpreted as an existential closure:

```lean
instance [State α] [AtPattern α P] : AtPattern α (A → P) where
  semantics pattern state :=
    ∃ argument, AtPattern.semantics (pattern argument) state
```

Consequently, a closure such as

```lean
fun x y : Conf => Conf.f x y
```

denotes all states of the form `Conf.f x y`. The binders `x` and `y` are the
pattern variables, but they are ordinary Lean binders rather than constructors
inside `Conf`.

Unifiability means that the two patterns denote a common state:

```lean
def Unifiable (p : P) (q : Q) : Prop :=
  ∃ state, AtPattern.semantics p state ∧ AtPattern.semantics q state

infix:50 " ⋈ " => Unifiable
```

For example, a hypothesis

```lean
h : pat1 ⋈ pat2
```

contains actual witnesses for every closure binder, as well as equalities from
both instantiated terms to one common state. The tactic opens those semantic
existentials and turns the two state equalities into the term equation that is
to be unified.

## 2. The namespaces are future file boundaries

The prototype remains in one file, but its responsibilities are separated as
if they were modules:

```text
Unification.Problem       read pattern closures and form a term equation
Unification.Certificate   describe backend-independent solution sets
Unification.Free          compute and certify free unifiers
Unification.Presentation  expose basis values and equations to users
Unification.Tactic        connect a semantic hypothesis to those components
```

The intended dependency direction is:

```text
semantic hypothesis
       |
       v
    Problem  --->  Free backend
                      |
                      v
                 Certificate
                      |
                      v
                Presentation
```

`Problem`, `Certificate`, and `Presentation` do not contain facts about the
example declarations `pat1`, `pat2`, `pairLeft`, or `pairRight`. All examples
occur below the tactic implementation.

## 3. Extracting a problem

`Problem.SaturatedPattern` records three pieces of information:

```lean
structure SaturatedPattern where
  application : Expr
  arguments : Array Expr
  argumentNames : Array Name
```

Suppose the input closure is

```lean
fun x1 x2 : Conf => f x1 x2
```

`saturatePattern` asks Lean for the closure's telescope and creates a fresh
metavariable for every explicit binder. Its `application` is conceptually

```text
f ?x1 ?x2
```

and `arguments` is `#[?x1, ?x2]`. Binder names are retained only so that the
proof-level witnesses can later be displayed as `x1` and `x2`.

The left and right closures are saturated independently. This is important:
the same printed name on the two sides does not mean that the variables were
shared. The semantic definition also quantifies the two closures independently.

`Problem.Input` simply pairs the two saturated closures. The order of
`Problem.symbolicArguments` is part of the interface:

```text
all left arguments, followed by all right arguments
```

Every later substitution image and every public equation follows this order.

## 4. Computing the free MGU

`Free.solve` invokes:

```lean
Lean.Meta.isDefEq problem.lhs.application problem.rhs.application
```

For constructor terms with fresh metavariables, Lean's definitional-equality
unifier performs ordinary free unification. It handles constructor
decomposition, cascading substitutions, and the occurs check.

For the equation

```text
f ?x1 ?x2 = f (f ?y1 c) c
```

Lean assigns

```text
?x1 := f ?y1 c
?x2 := c
```

and leaves `?y1` unassigned. An unassigned metavariable is not an error: it is
an independent parameter of the MGU.

### Why native metavariables must stop at the backend

A `MVarId` is mutable elaborator state. It is meaningful only while Lean is
running this particular unification computation. It would be a poor public
representation and could not be produced by a text-based external oracle.

Therefore `Free.solve` immediately abstracts every residual metavariable. If
`?y1` is the only residual, the raw images

```text
f ?y1 c
c
?y1
```

become closed lambda templates:

```text
fun u1 => f u1 c
fun u1 => c
fun u1 => u1
```

Only these lambdas and the type of `u1` cross into
`Certificate.Alternative`:

```lean
structure Alternative where
  basisTypes : Array Expr
  images : Array Expr
```

There are no backend-owned metavariables in this structure.

## 5. What a basis variable means

A basis variable is a parameter of a unifier, not an object-language term and
not an unresolved Lean hole. For the preceding example the branch means:

```lean
∃ u1 : Conf,
  x1 = f u1 c ∧
  x2 = c ∧
  y1 = u1 ∧
  True
```

The final `True` is only a convenient terminator for a generated conjunction.
The presentation layer removes it.

In free unification every residual parameter can be witnessed by one of the
original semantic arguments. `Free.Candidate.basisWitnesses` records those
indices solely for proof reconstruction. This field is private to the free
backend; it is deliberately absent from `Certificate.Alternative`.

That distinction is essential for AC unification. An AC basis value may be a
new intersection component that is not equal to any one original variable.
Such a backend must prove its factorization by its own certificate replay, but
it can still return exactly the same `Alternative` structure.

## 6. Solution sets, including future AC alternatives

Free first-order unification is unitary: a supported problem has either no MGU
or one MGU. The common certificate format does not bake in that fact:

```lean
structure SolutionSet where
  alternatives : Array Alternative
```

Its logical interpretation is:

```text
zero alternatives:   False
one alternative:     factorization₁
several alternatives: factorization₁ ∨ ... ∨ factorizationₙ
```

`Certificate.ProvenSolutionSet` contains both this description and an `Expr`
whose type is the corresponding proposition. When the proof is added to a Lean
goal, Lean's kernel checks its type. Candidate substitutions by themselves are
not trusted.

`Presentation.expose` already understands all three cardinalities:

- An empty result supplies `False` and closes the current goal.
- A singleton result opens one factorization.
- A multi-result certificate splits the proof into one Lean goal per
  alternative and opens each factorization in the same way.

Thus a future AC backend changes how alternatives and their coverage proof are
computed. It does not have to change the per-branch user interface.

## 7. Success certification

Calling `isDefEq` computes a candidate, but it does not become a theorem in the
user's proof. The tactic separately reconstructs a proof.

`Tactic.exposeSemantics` opens `h : p ⋈ q`. For the main example it obtains
locals resembling:

```text
x1 x2 y1 : Conf
_unifyLhs : pat1 x1 x2 = _unifyState
_unifyRhs : pat2 y1 = _unifyState
```

It composes the two equalities:

```text
pat1 x1 x2 = pat2 y1
```

and unfolds the pattern definitions, obtaining:

```text
f x1 x2 = f (f y1 c) c
```

`Free.certifySuccess` next creates the factorization proposition selected by
the native substitution. In the free theory it uses the recorded original
arguments as existential witnesses and asks `simp_all` to prove every generated
equation from the constructor equality.

This separation is a safety boundary:

```text
native unification chooses the proposed MGU
Lean proof reconstruction establishes that proposal
the kernel checks the resulting proof term
```

If the proposed images were wrong, factorization certification would fail.

## 8. Failure certification

An empty result must also be justified. It is not sound to close a proof merely
because `isDefEq` returned `false`.

There are two relevant failure shapes.

### Constructor clash

For

```lean
(fun x : Conf => f x x) ⋈ c
```

the semantic hypothesis implies `f x x = c`. Constructor discrimination lets
`simp_all` prove `False` directly.

### Occurs-check cycle

Consider:

```lean
(fun x : Conf => f x x) ⋈
  (fun y : Conf => f (f y c) y)
```

Constructor injectivity implies both

```text
x = f y c
x = y
```

and hence a cyclic equation. Merely simplifying constructor equality does not
always close this case. `Free.certifyFailureGoal` maps every equality leaf
through `SizeOf.sizeOf` using `congrArg`. Generated inductive `SizeOf` equations
turn a proper-subterm cycle into impossible natural-number arithmetic. Lean's
`omega` tactic then checks that contradiction.

This works for ordinary inductive free-term models, for which Lean generates a
`SizeOf` instance. If a custom state representation suppresses or replaces
that structural size, an occurs-check refutation may require a backend-specific
well-founded measure.

## 9. Presenting the result

The presentation layer eliminates the existential factorization proof. It
renames its witnesses deterministically:

```text
u1, u2, ...
```

It then eliminates the conjunction and renames equations in original-argument
order:

```text
h1, h2, ...
```

For `pat1 ⋈ pat2`, the context after `unify h` is:

```lean
x1 x2 y1 u1 : Conf
h1 : x1 = f u1 c
h2 : x2 = c
h3 : y1 = u1
```

Names are made fresh against the surrounding context. In an ordinary example
they are exactly `u1` and `h1`; if those names already exist, Lean receives a
fresh variant rather than a collision.

The internal common state, semantic equalities, combined constructor equality,
and trailing `True` proof are cleared. Users see only the original closure
witnesses, basis values, and substitution equations.

## 10. Reading the regression examples

The examples below the implementation use `guard_hyp` to test the interface.
For example:

```lean
example (h : pairLeft ⋈ pairRight) : True := by
  unify h
  guard_hyp u1 : Conf
  guard_hyp u2 : Conf
  guard_hyp h1 : x1 = f u1 u2
  guard_hyp h2 : x2 = f u2 u1
  guard_hyp h3 : y1 = u1
  guard_hyp h4 : y2 = u2
  exact True.intro
```

These checks matter more than ending the example with `True.intro`: they ensure
that refactoring does not silently change basis count, equation order, or
substitution images.

Other examples cover:

- inline lambda closures, showing that no declaration names are hard-coded;
- two pure variables, showing that the basis is a Lean local;
- cascading nested substitutions;
- a ground equation, which has no basis variables or equations;
- a constructor clash; and
- an occurs-check cycle.

## 11. The supported free fragment

This is a proof-of-concept tactic for first-order constructor terms. A proper
input currently has these characteristics:

- The hypothesis has the form `h : p ⋈ q`.
- Pattern variables are explicit Lean closure arguments.
- Instantiating each closure produces an ordinary term in a free inductive
  constructor model.
- The atomic semantics eventually reduces to equality with the common state.
- For cyclic failure certification, the term model has a structural `SizeOf`
  instance, as normal Lean inductives do.

The tactic deliberately reports an error instead of pretending to solve an
unsupported input. Current non-goals include higher-order unification,
theory-specific equations such as associativity or commutativity, dependent
basis types, implicit pattern binders, and arbitrary side conditions in atomic
patterns.

Within the constructor fragment, native unification terminates with the unique
MGU or failure, and both outcomes are independently certified in Lean.

## 12. Replacing the backend for AC or ACU

The free-specific boundary is the `Unification.Free` namespace. It currently
does three jobs:

1. Compute candidates with `isDefEq`.
2. Abstract residual metavariables into basis-parametric images.
3. Prove complete coverage of the returned zero-or-one result.

An AC implementation would replace those jobs with, for example:

```text
parse/reify the constructor equation
invoke an AC solver or external oracle
convert every returned substitution to Certificate.Alternative
replay a certificate in Lean to prove the disjunction of factorizations
```

The external output cannot be trusted merely because it came from Maude. The
Lean side must verify soundness of each substitution and completeness of the
returned set, or consume a theorem/certificate that establishes both. Once it
constructs `Certificate.ProvenSolutionSet`, the existing presentation code
handles basis naming, equations, and branch splitting.

Maude-style basis variables such as `%1` and `%2` map naturally to
`basisTypes`. A binding such as

```text
X --> f(%1, %2)
```

becomes a lambda image like

```lean
fun u1 u2 => f u1 u2
```

Bindings must be reordered by original variable identity into the canonical
left-then-right argument order. Their textual output order must not determine
the public `h1`, `h2`, ... numbering.

The public proof script remains:

```lean
ac_unify h
```

and each resulting goal has the same shape as a goal produced by `unify h`.
The expected difference is only that AC or ACU may produce several goals.

## 13. End-to-end summary

For a successful call `unify h`, the complete path is:

1. Read `p` and `q` from the type of `h`.
2. Saturate their explicit closure binders with fresh metavariables.
3. Run Lean's native definitional-equality unifier.
4. Abstract residual metavariables into closed basis lambdas.
5. Open the semantic witnesses contained in `h`.
6. Derive the concrete constructor equality through the shared state.
7. Prove the existential factorization selected by the computed MGU.
8. Open that proof as `u1`, `u2`, ... and `h1`, `h2`, ....
9. Clear all implementation-only semantic bookkeeping.

For failure, steps 7 and 8 are replaced by a checked proof of `False`, after
which the original goal is closed by contradiction.

This architecture keeps the pleasant part of Lean-native free unification
while making the output independent of Lean's mutable metavariables and ready
for a future multi-unifier backend.
