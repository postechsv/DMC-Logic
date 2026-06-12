--import Mathlib.Tactic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Multiset.Bind

namespace ACUCert

open Lean Meta Elab Tactic

structure BranchShape where
  numExists : Nat
  numEqs    : Nat
deriving Repr

def isAppOfConst (e : Expr) (n : Name) : Bool :=
  e.getAppFn.isConstOf n

partial def flattenOr (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  let args := e.getAppArgs
  if isAppOfConst e ``Or && args.size == 2 then
    let xs ← flattenOr args[0]!
    let ys ← flattenOr args[1]!
    pure (xs ++ ys)
  else
    pure #[e]

partial def flattenAnd (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  let args := e.getAppArgs
  if isAppOfConst e ``And && args.size == 2 then
    let xs ← flattenAnd args[0]!
    let ys ← flattenAnd args[1]!
    pure (xs ++ ys)
  else
    pure #[e]

def decomposeEq? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let e ← whnf e
  let args := e.getAppArgs
  if isAppOfConst e ``Eq && args.size == 3 then
    -- Eq.{u} α lhs rhs
    pure (some (args[0]!, args[1]!, args[2]!))
  else
    pure none

/--
Open nested existentials in a branch.

A branch has shape:

  ∃ U₁ ... Uₖ, body

This function opens the binders as fresh local variables and then calls `k`
on:

  - the fresh existential variables;
  - the body with those variables substituted in.

Important: do not return expressions containing these fresh variables outside
the continuation. Use them inside the continuation.
-/
partial def withPeelExists
    {β : Type}
    (e : Expr)
    (acc : Array Expr)
    (k : Array Expr → Expr → MetaM β) :
    MetaM β := do
  let e ← whnf e
  if isAppOfConst e ``Exists then
    let args := e.getAppArgs
    if args.size < 1 then
      throwError "Malformed Exists expression:\n{e}"

    let pred := args[args.size - 1]!

    match pred with
    | Expr.lam n ty body bi =>
        withLocalDecl n bi ty fun x => do
          let body' := body.instantiate1 x
          withPeelExists body' (acc.push x) k
    | _ =>
        throwError "Expected Exists predicate to be a lambda, got:\n{pred}"
  else
    k acc e

def getFVarDeclFromExpr (e : Expr) : MetaM LocalDecl := do
  match e with
  | Expr.fvar id => id.getDecl
  | _ => throwError "Expected free variable, got:\n{e}"

/--
Inspect one certificate branch.

A branch should have shape:

  ∃ U₁ ... Uₖ, eq₁ ∧ ... ∧ eqₘ
-/
def inspectBranch (i : Nat) (branch : Expr) : MetaM Unit := do
  withPeelExists branch #[] fun xs core => do
    let conjuncts ← flattenAnd core

    logInfo m!"branch {i}: exists = {xs.size}, equations = {conjuncts.size}"

    for j in [:xs.size] do
      let decl ← getFVarDeclFromExpr xs[j]!
      logInfo m!"  exists {j}: {decl.userName} : {decl.type}"

    for j in [:conjuncts.size] do
      let c := conjuncts[j]!
      match (← decomposeEq? c) with
      | some (ty, lhs, rhs) =>
          logInfo m!"  equation {j}:"
          logInfo m!"    type: {ty}"
          logInfo m!"    lhs : {lhs}"
          logInfo m!"    rhs : {rhs}"
      | none =>
          throwError "Expected equality conjunct in branch {i}, got:\n{c}"

/--
Peel a nondependent implication:

  premise → certificate
-/
def peelImp (target : Expr) : MetaM (Expr × Expr) := do
  let target ← whnf target
  match target with
  | Expr.forallE _ prem body _ =>
      if body.hasLooseBVars then
        throwError "Dependent implication/forall not supported in this parser milestone"
      else
        pure (prem, body)
  | _ =>
      throwError "Expected goal of the form premise → certificate, got:\n{target}"

/--
Generic certificate-grammar inspector.

This does not prove anything yet. It parses the goal as:

  premise → branch₁ ∨ ... ∨ branchₙ

where each branch is:

  ∃ U₁ ... Uₖ, eq₁ ∧ ... ∧ eqₘ
-/
elab "acu_cert_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let branches ← flattenOr cert

    logInfo m!"ACU premise:\n{prem}"
    logInfo m!"number of branches: {branches.size}"

    for i in [:branches.size] do
      inspectBranch i branches[i]!


end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_inspect
  sorry

end ACUCert


namespace ACUCert

open Lean Meta Elab Tactic

/--
Recognize a literal `0` inside an `OfNat.ofNat` application.
This is deliberately permissive because elaborated numerals include typeclass
arguments.
-/
def hasNatLitZero (args : Array Expr) : Bool :=
  args.any fun a =>
    match a with
    | Expr.lit (Literal.natVal 0) => true
    | _ => false

/--
Recognize expressions elaborated from `0`.

Important: do NOT `whnf` here. For `Multiset`, unfolding `0` may expose
implementation details rather than the syntactic neutral element.
-/
def isZeroLike (e : Expr) : Bool :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  (fn.isConstOf ``OfNat.ofNat && hasNatLitZero args) ||
  fn.isConstOf ``Zero.zero

/--
Return the two operands of an elaborated `+` expression, if this expression
is syntactically an addition.

For overloaded `+`, Lean usually elaborates through `HAdd.hAdd`.
The actual operands are the last two application arguments..

Important: do NOT `whnf` here. For `Multiset`, `whnf` unfolds addition into
`Quot.lift ...`, destroying the syntactic `+` structure we want to parse.

For overloaded `+`, Lean normally elaborates through `HAdd.hAdd`.
The actual operands are the last two application arguments.
-/
def getAddOperands? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs

  if fn.isConstOf ``HAdd.hAdd && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else if fn.isConstOf ``Add.add && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

/--
Flatten an ACU expression into summands.

Examples conceptually:

  X + Y              ↦ #[X, Y]
  (X + Y) + A        ↦ #[X, Y, A]
  X + 0              ↦ #[X]
  ({1} : Multiset Nat) + {2} ↦ #[{1}, {2}]

This does not yet sort, combine coefficients, or classify atoms.

This deliberately avoids `whnf`, because unfolding `Multiset.add` hides the
surface-level ACU structure.
-/
partial def flattenACUExpr (e : Expr) : MetaM (Array Expr) := do
  if isZeroLike e then
    pure #[]
  else
    match getAddOperands? e with
    | some (lhs, rhs) =>
        let xs ← flattenACUExpr lhs
        let ys ← flattenACUExpr rhs
        pure (xs ++ ys)
    | none =>
        pure #[e]

def logFlattenedACUExpr (label : String) (e : Expr) : MetaM Unit := do
  let terms ← flattenACUExpr e
  logInfo m!"{label}: {terms.size} summand(s)"
  for i in [:terms.size] do
    logInfo m!"  [{i}] {terms[i]!}"

/--
Inspect an equality as an ACU equality by flattening both sides.
-/
def inspectACUEq (label : String) (eqExpr : Expr) : MetaM Unit := do
  match (← decomposeEq? eqExpr) with
  | some (_ty, lhs, rhs) =>
      logInfo m!"{label}:"
      logFlattenedACUExpr "  lhs" lhs
      logFlattenedACUExpr "  rhs" rhs
  | none =>
      throwError "Expected equality, got:\n{eqExpr}"

/--
A stronger inspector: parse the whole certificate grammar and also flatten
each premise/branch equality as ACU expressions.
-/
elab "acu_cert_norm_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let branches ← flattenOr cert

    logInfo m!"ACU premise raw:\n{prem}"
    inspectACUEq "ACU premise normalized" prem

    logInfo m!"number of branches: {branches.size}"

    for i in [:branches.size] do
      let branch := branches[i]!
      withPeelExists branch #[] fun xs core => do
        let conjuncts ← flattenAnd core

        logInfo m!"branch {i}: exists = {xs.size}, equations = {conjuncts.size}"

        for j in [:xs.size] do
          let decl ← getFVarDeclFromExpr xs[j]!
          logInfo m!"  exists {j}: {decl.userName} : {decl.type}"

        for j in [:conjuncts.size] do
          inspectACUEq s!"  branch {i}, equation {j}" conjuncts[j]!

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_norm_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_norm_inspect
  sorry

end ACUCert


namespace ACUCert

open Lean Meta Elab Tactic

/--
A summand in a normalized ACU expression.

For example:

  X + X + Y

becomes:

  [{ atom := X, coeff := 2 },
   { atom := Y, coeff := 1 }]
-/
structure ACUSummand where
  atom  : Expr
  coeff : Nat

abbrev ACUForm := Array ACUSummand

/--
Structural equality on expressions.

This is enough for the current parser milestone, because repeated occurrences
of the same local variable or same ground singleton usually elaborate to
structurally identical expressions.
-/
def sameAtom (a b : Expr) : Bool :=
  a == b

/--
Add one atom to an ACU linear form, increasing its coefficient if it is
already present.
-/
partial def addAtomToForm (form : ACUForm) (a : Expr) : ACUForm :=
  let rec go (i : Nat) : ACUForm :=
    if h : i < form.size then
      let item := form[i]
      if sameAtom item.atom a then
        form.set i { item with coeff := item.coeff + 1 }
      else
        go (i + 1)
    else
      form.push { atom := a, coeff := 1 }
  go 0

/--
Convert a flattened ACU expression into a coefficient form.
-/
def normalizeACUExpr (e : Expr) : MetaM ACUForm := do
  let atoms ← flattenACUExpr e
  pure (atoms.foldl addAtomToForm #[])

/--
Pretty logging for an ACU linear form.
-/
def logACUForm (label : String) (form : ACUForm) : MetaM Unit := do
  logInfo m!"{label}: {toString form.size} distinct summand(s)"
  let mut i : Nat := 0
  for s in form do
    logInfo m!"  index {toString i}, coeff {toString s.coeff}: {s.atom}"
    i := i + 1

/--
Inspect an equality as normalized ACU linear forms.
-/
def inspectACUEqLinear (label : String) (eqExpr : Expr) : MetaM Unit := do
  match (← decomposeEq? eqExpr) with
  | some (_ty, lhs, rhs) =>
      let lhsForm ← normalizeACUExpr lhs
      let rhsForm ← normalizeACUExpr rhs
      logInfo m!"{label}:"
      logACUForm "  lhs" lhsForm
      logACUForm "  rhs" rhsForm
  | none =>
      throwError "Expected equality, got:\n{eqExpr}"

/--
Inspector that parses the certificate grammar and prints normalized ACU
linear forms for every equality.
-/
elab "acu_cert_linear_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let branches ← flattenOr cert

    logInfo m!"ACU premise raw:\n{prem}"
    inspectACUEqLinear "ACU premise linearized" prem

    logInfo m!"number of branches: {branches.size}"

    for i in [:branches.size] do
      let branch := branches[i]!
      withPeelExists branch #[] fun xs core => do
        let conjuncts ← flattenAnd core

        logInfo m!"branch {i}: exists = {xs.size}, equations = {conjuncts.size}"

        for j in [:xs.size] do
          let decl ← getFVarDeclFromExpr xs[j]!
          logInfo m!"  exists {j}: {decl.userName} : {decl.type}"

        for j in [:conjuncts.size] do
          inspectACUEqLinear s!"  branch {i}, equation {j}" conjuncts[j]!

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_linear_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_linear_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_linear_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
A normalized ACU equality.
-/
structure ACUEqForm where
  lhs : ACUForm
  rhs : ACUForm

def normalizeACUEq (eqExpr : Expr) : MetaM ACUEqForm := do
  match (← decomposeEq? eqExpr) with
  | some (_ty, lhs, rhs) =>
      let lhsForm ← normalizeACUExpr lhs
      let rhsForm ← normalizeACUExpr rhs
      pure { lhs := lhsForm, rhs := rhsForm }
  | none =>
      throwError "Expected equality, got:\n{eqExpr}"

/--
Add an atom to an atom list if not already present.
-/
def pushAtomIfMissing (atoms : Array Expr) (a : Expr) : Array Expr :=
  if atoms.any (fun b => sameAtom a b) then
    atoms
  else
    atoms.push a

def collectAtomsFromForm (atoms : Array Expr) (form : ACUForm) : Array Expr :=
  Id.run do
    let mut out := atoms
    for s in form do
      out := pushAtomIfMissing out s.atom
    return out

def collectAtomsFromEq (atoms : Array Expr) (eqn : ACUEqForm) : Array Expr :=
  let atoms := collectAtomsFromForm atoms eqn.lhs
  collectAtomsFromForm atoms eqn.rhs

def coeffOf (form : ACUForm) (a : Expr) : Nat :=
  Id.run do
    let mut out : Nat := 0
    for s in form do
      if sameAtom s.atom a then
        out := s.coeff
    return out

def logAtoms (atoms : Array Expr) : MetaM Unit := do
  logInfo m!"atoms: {toString atoms.size}"
  let mut i : Nat := 0
  for a in atoms do
    logInfo m!"  atom {toString i}: {a}"
    i := i + 1

/--
Log one normalized equation as coefficient vectors over a fixed atom basis.
-/
def logEqVector (label : String) (atoms : Array Expr) (eqn : ACUEqForm) : MetaM Unit := do
  logInfo m!"{label}:"
  let mut i : Nat := 0
  for a in atoms do
    let lc := coeffOf eqn.lhs a
    let rc := coeffOf eqn.rhs a
    if lc ≠ 0 || rc ≠ 0 then
      logInfo m!"  atom {toString i}: lhs coeff {toString lc}, rhs coeff {toString rc}, atom {a}"
    i := i + 1

/--
Generic vector inspector.

For each branch, it builds one shared atom basis containing:
  - atoms from the premise;
  - atoms from all equations in that branch.

Then it prints coefficient vectors for the premise and branch equations.
-/
elab "acu_cert_vector_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let premEq ← normalizeACUEq prem
    let branches ← flattenOr cert

    logInfo m!"number of branches: {branches.size}"

    let mut branchIndex : Nat := 0
    for branch in branches do
      withPeelExists branch #[] fun xs core => do
        let conjuncts ← flattenAnd core

        let mut branchEqs : Array ACUEqForm := #[]
        for c in conjuncts do
          branchEqs := branchEqs.push (← normalizeACUEq c)

        let mut atoms : Array Expr := #[]
        atoms := collectAtomsFromEq atoms premEq
        for eqn in branchEqs do
          atoms := collectAtomsFromEq atoms eqn

        logInfo m!"branch {toString branchIndex}: exists = {toString xs.size}, equations = {toString branchEqs.size}"
        logAtoms atoms
        logEqVector "  premise vector" atoms premEq

        let mut eqIndex : Nat := 0
        for eqn in branchEqs do
          logEqVector s!"  branch equation {eqIndex}" atoms eqn
          eqIndex := eqIndex + 1

      branchIndex := branchIndex + 1

end ACUCert


namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_vector_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_vector_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_vector_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

inductive AtomKind where
  | fixed
  | existential (idx : Nat)
deriving Repr

def atomKindToString : AtomKind → String
  | .fixed => "fixed"
  | .existential i => "existential " ++ toString i

def findAtomIndex (xs : Array Expr) (a : Expr) : Option Nat :=
  Id.run do
    let mut out : Option Nat := none
    let mut i : Nat := 0
    for x in xs do
      match out with
      | some _ => pure ()
      | none =>
          if sameAtom x a then
            out := some i
      i := i + 1
    return out

def classifyAtom (existsVars : Array Expr) (a : Expr) : AtomKind :=
  match findAtomIndex existsVars a with
  | some i => .existential i
  | none => .fixed

def logAtomsClassified (existsVars : Array Expr) (atoms : Array Expr) : MetaM Unit := do
  logInfo m!"atoms: {toString atoms.size}"
  let mut i : Nat := 0
  for a in atoms do
    let kind := classifyAtom existsVars a
    logInfo m!"  atom {toString i}: {atomKindToString kind}, {a}"
    i := i + 1

def logEqVectorClassified
    (label : String)
    (existsVars : Array Expr)
    (atoms : Array Expr)
    (eqn : ACUEqForm) :
    MetaM Unit := do
  logInfo m!"{label}:"
  let mut i : Nat := 0
  for a in atoms do
    let lc := coeffOf eqn.lhs a
    let rc := coeffOf eqn.rhs a
    if lc ≠ 0 || rc ≠ 0 then
      let kind := classifyAtom existsVars a
      logInfo
        m!"  atom {toString i}: {atomKindToString kind}, lhs coeff {toString lc}, rhs coeff {toString rc}, atom {a}"
    i := i + 1

/--
Like `acu_cert_vector_inspect`, but also classifies each atom as either
fixed or existential-with-index.

This is a generic step toward deciding which count variables are inputs and
which ones are branch witnesses.
-/
elab "acu_cert_classify_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let premEq ← normalizeACUEq prem
    let branches ← flattenOr cert

    logInfo m!"number of branches: {toString branches.size}"

    let mut branchIndex : Nat := 0
    for branch in branches do
      withPeelExists branch #[] fun xs core => do
        let conjuncts ← flattenAnd core

        let mut branchEqs : Array ACUEqForm := #[]
        for c in conjuncts do
          branchEqs := branchEqs.push (← normalizeACUEq c)

        let mut atoms : Array Expr := #[]
        atoms := collectAtomsFromEq atoms premEq
        for eqn in branchEqs do
          atoms := collectAtomsFromEq atoms eqn

        logInfo m!"branch {toString branchIndex}: exists = {toString xs.size}, equations = {toString branchEqs.size}"

        for j in [:xs.size] do
          let decl ← getFVarDeclFromExpr xs[j]!
          logInfo m!"  exists {toString j}: {decl.userName} : {decl.type}"

        logAtomsClassified xs atoms
        logEqVectorClassified "  premise vector" xs atoms premEq

        let mut eqIndex : Nat := 0
        for eqn in branchEqs do
          logEqVectorClassified s!"  branch equation {eqIndex}" xs atoms eqn
          eqIndex := eqIndex + 1

      branchIndex := branchIndex + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_classify_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_classify_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_classify_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
A signed coefficient row represents one linear equation:

  Σ coeff(atomᵢ) * count(e, atomᵢ) = 0

The coefficient is lhsCoeff - rhsCoeff.
-/
structure SignedCoeff where
  atom  : Expr
  kind  : AtomKind
  coeff : Int

abbrev SignedRow := Array SignedCoeff

def signedCoeffOf (eqn : ACUEqForm) (a : Expr) : Int :=
  let lc := coeffOf eqn.lhs a
  let rc := coeffOf eqn.rhs a
  (Int.ofNat lc) - (Int.ofNat rc)

def compileSignedRow
    (existsVars : Array Expr)
    (atoms : Array Expr)
    (eqn : ACUEqForm) :
    SignedRow :=
  Id.run do
    let mut row : SignedRow := #[]
    for a in atoms do
      let c := signedCoeffOf eqn a
      if c = 0 then
        pure ()
      else
        row := row.push {
          atom := a
          kind := classifyAtom existsVars a
          coeff := c
        }
    return row

def logSignedRow (label : String) (row : SignedRow) : MetaM Unit := do
  logInfo m!"{label}:"
  if row.isEmpty then
    logInfo m!"  0 = 0"
  else
    for t in row do
      logInfo
        m!"  coeff {toString t.coeff}, {atomKindToString t.kind}, atom {t.atom}"

/--
A branch matrix consists of:
  - one premise row;
  - several branch rows.

All rows are over the same atom basis.
-/
structure BranchMatrix where
  existsVars : Array Expr
  atoms      : Array Expr
  premise    : SignedRow
  branchRows : Array SignedRow

def buildBranchMatrix
    (premEq : ACUEqForm)
    (existsVars : Array Expr)
    (branchEqs : Array ACUEqForm) :
    BranchMatrix :=
  Id.run do
    let mut atoms : Array Expr := #[]
    atoms := collectAtomsFromEq atoms premEq
    for eqn in branchEqs do
      atoms := collectAtomsFromEq atoms eqn

    let premiseRow := compileSignedRow existsVars atoms premEq

    let mut rows : Array SignedRow := #[]
    for eqn in branchEqs do
      rows := rows.push (compileSignedRow existsVars atoms eqn)

    return {
      existsVars := existsVars
      atoms := atoms
      premise := premiseRow
      branchRows := rows
    }

def logBranchMatrix (idx : Nat) (m : BranchMatrix) : MetaM Unit := do
  logInfo m!"branch {toString idx}:"
  logInfo m!"  existential vars: {toString m.existsVars.size}"
  logInfo m!"  atoms: {toString m.atoms.size}"
  logSignedRow "  premise row" m.premise

  let mut i : Nat := 0
  for row in m.branchRows do
    logSignedRow s!"  branch row {i}" row
    i := i + 1

/--
Inspect the generic arithmetic matrix induced by the certificate.

This is now independent of ex1/ex2/etc.
-/
elab "acu_cert_matrix_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let premEq ← normalizeACUEq prem
    let branches ← flattenOr cert

    logInfo m!"number of branches: {toString branches.size}"

    let mut branchIndex : Nat := 0
    for branch in branches do
      withPeelExists branch #[] fun xs core => do
        let conjuncts ← flattenAnd core

        let mut branchEqs : Array ACUEqForm := #[]
        for c in conjuncts do
          branchEqs := branchEqs.push (← normalizeACUEq c)

        let matrix := buildBranchMatrix premEq xs branchEqs
        logBranchMatrix branchIndex matrix

      branchIndex := branchIndex + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_matrix_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_matrix_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_matrix_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Get the element type `α` from an atom of type `Multiset α`.
-/
def getElemTypeOfMultisetAtom (atom : Expr) : MetaM Expr := do
  let ty ← inferType atom
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf ``Multiset && args.size == 1 then
    pure args[0]!
  else
    throwError "Expected atom of type Multiset α, got atom:\n{atom}\nwith type:\n{ty}"

/--
Build `Multiset.count e atom`.
-/
def mkCountExpr (e atom : Expr) : MetaM Expr := do
  mkAppM ``Multiset.count #[e, atom]

/--
Build `n * t`, but avoid multiplication by 1.
-/
def mkCoeffTimes (n : Nat) (t : Expr) : MetaM Expr := do
  if n = 0 then
    pure (mkNatLit 0)
  else if n = 1 then
    pure t
  else
    mkAppM ``Nat.mul #[mkNatLit n, t]

/--
Build a Nat sum from terms.

The empty sum is 0.
-/
def mkNatSum (terms : Array Expr) : MetaM Expr := do
  if h : 0 < terms.size then
    let mut acc : Expr := terms[0]
    let mut i : Nat := 1
    while hlt : i < terms.size do
      acc ← mkAppM ``Nat.add #[acc, terms[i]]
      i := i + 1
    pure acc
  else
    pure (mkNatLit 0)

/--
Convert a signed row

  Σ cᵢ * count e atomᵢ = 0

into a Nat equality by moving positive coefficients to the lhs and
negative coefficients to the rhs.

Example:

  2·X - A - B = 0

becomes:

  2 * count e X = count e A + count e B
-/
def signedRowToNatEqExpr (e : Expr) (row : SignedRow) : MetaM Expr := do
  let mut lhsTerms : Array Expr := #[]
  let mut rhsTerms : Array Expr := #[]

  for t in row do
    let countTerm ← mkCountExpr e t.atom

    if t.coeff > 0 then
      let n := Int.toNat t.coeff
      let term ← mkCoeffTimes n countTerm
      lhsTerms := lhsTerms.push term
    else if t.coeff < 0 then
      let n := Int.toNat (-t.coeff)
      let term ← mkCoeffTimes n countTerm
      rhsTerms := rhsTerms.push term
    else
      pure ()

  let lhs ← mkNatSum lhsTerms
  let rhs ← mkNatSum rhsTerms
  mkAppM ``Eq #[lhs, rhs]

/--
Log the Nat equality proposition induced by a signed row.
-/
def logRowAsNatEq (label : String) (e : Expr) (row : SignedRow) : MetaM Unit := do
  let prop ← signedRowToNatEqExpr e row
  logInfo m!"{label}: {prop}"

/--
For one branch matrix, introduce a fresh arbitrary element `e : α`,
then print the arithmetic count equations for the premise and each branch row.
-/
def inspectBranchArithmetic (idx : Nat) (m : BranchMatrix) : MetaM Unit := do
  if h : 0 < m.atoms.size then
    let atom0 := m.atoms[0]
    let elemTy ← getElemTypeOfMultisetAtom atom0

    withLocalDeclD `e elemTy fun e => do
      logInfo m!"branch {toString idx}: arithmetic view with element e : {elemTy}"
      logRowAsNatEq "  premise arithmetic" e m.premise

      let mut i : Nat := 0
      for row in m.branchRows do
        logRowAsNatEq s!"  branch equation {i} arithmetic" e row
        i := i + 1
  else
    throwError "Cannot infer element type: branch has no atoms"

/--
Generic arithmetic-proposition inspector.

This parses the certificate, normalizes each ACU equality into signed rows,
and then displays the induced pointwise Nat equations.

Still no proving yet.
-/
elab "acu_cert_arith_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let premEq ← normalizeACUEq prem
    let branches ← flattenOr cert

    logInfo m!"number of branches: {toString branches.size}"

    let mut branchIndex : Nat := 0
    for branch in branches do
      withPeelExists branch #[] fun xs core => do
        let conjuncts ← flattenAnd core

        let mut branchEqs : Array ACUEqForm := #[]
        for c in conjuncts do
          branchEqs := branchEqs.push (← normalizeACUEq c)

        let matrix := buildBranchMatrix premEq xs branchEqs
        inspectBranchArithmetic branchIndex matrix

      branchIndex := branchIndex + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_arith_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_arith_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_arith_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Build a count-like Nat term for an atom.

If the atom is fixed, use:

  Multiset.count e atom

If the atom is an existential certificate parameter, use the corresponding
fresh Nat witness variable.
-/
def mkAtomNatTerm
    (e : Expr)
    (uVars : Array Expr)
    (t : SignedCoeff) :
    MetaM Expr := do
  match t.kind with
  | .fixed =>
      mkCountExpr e t.atom
  | .existential i =>
      if h : i < uVars.size then
        pure uVars[i]
      else
        throwError
          "Existential index out of bounds: {toString i}, number of vars = {toString uVars.size}"

/--
Convert a signed row to a Nat equality, using fresh Nat variables for
existential atoms.

Example row:

  X - U - V - W = 0

becomes:

  count e X = u + v + w
-/
def signedRowToNatEqExprWithEVars
    (e : Expr)
    (uVars : Array Expr)
    (row : SignedRow) :
    MetaM Expr := do
  let mut lhsTerms : Array Expr := #[]
  let mut rhsTerms : Array Expr := #[]

  for t in row do
    let base ← mkAtomNatTerm e uVars t

    if t.coeff > 0 then
      let n := Int.toNat t.coeff
      let term ← mkCoeffTimes n base
      lhsTerms := lhsTerms.push term
    else if t.coeff < 0 then
      let n := Int.toNat (-t.coeff)
      let term ← mkCoeffTimes n base
      rhsTerms := rhsTerms.push term
    else
      pure ()

  let lhs ← mkNatSum lhsTerms
  let rhs ← mkNatSum rhsTerms
  mkAppM ``Eq #[lhs, rhs]

def logRowAsNatEqWithEVars
    (label : String)
    (e : Expr)
    (uVars : Array Expr)
    (row : SignedRow) :
    MetaM Unit := do
  let prop ← signedRowToNatEqExprWithEVars e uVars row
  logInfo m!"{label}: {prop}"

/--
Introduce Nat variables u0, u1, ..., one for each existential multiset
parameter of the branch.
-/
partial def withNatWitnessVars
    {β : Type}
    (n : Nat)
    (acc : Array Expr)
    (k : Array Expr → MetaM β) :
    MetaM β := do
  if h : acc.size < n then
    let idx := acc.size
    withLocalDeclD (Name.mkSimple ("u" ++ toString idx)) (mkConst ``Nat) fun u => do
      withNatWitnessVars n (acc.push u) k
  else
    k acc

/--
Inspect the pointwise arithmetic problem for one branch.

Fixed atoms become `count e fixedAtom`.
Existential multiset atoms become fresh Nat variables.
-/
def inspectBranchPointwiseProblem (idx : Nat) (m : BranchMatrix) : MetaM Unit := do
  if h : 0 < m.atoms.size then
    let atom0 := m.atoms[0]
    let elemTy ← getElemTypeOfMultisetAtom atom0

    withLocalDeclD `e elemTy fun e => do
      withNatWitnessVars m.existsVars.size #[] fun uVars => do
        logInfo m!"branch {toString idx}: pointwise arithmetic problem"
        logInfo m!"  arbitrary element e : {elemTy}"

        for i in [:uVars.size] do
          logInfo m!"  witness count u{toString i} : Nat"

        logRowAsNatEqWithEVars "  premise" e uVars m.premise

        let mut i : Nat := 0
        for row in m.branchRows do
          logRowAsNatEqWithEVars s!"  branch equation {i}" e uVars row
          i := i + 1
  else
    throwError "Cannot infer element type: branch has no atoms"

/--
Inspector for the generic pointwise branch problems.

This is very close to the arithmetic certificate checker we eventually need.
-/
elab "acu_cert_pointwise_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let target ← instantiateMVars target
    let (prem, cert) ← peelImp target
    let premEq ← normalizeACUEq prem
    let branches ← flattenOr cert

    logInfo m!"number of branches: {toString branches.size}"

    let mut branchIndex : Nat := 0
    for branch in branches do
      withPeelExists branch #[] fun xs core => do
        let conjuncts ← flattenAnd core

        let mut branchEqs : Array ACUEqForm := #[]
        for c in conjuncts do
          branchEqs := branchEqs.push (← normalizeACUEq c)

        let matrix := buildBranchMatrix premEq xs branchEqs
        inspectBranchPointwiseProblem branchIndex matrix

      branchIndex := branchIndex + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_pointwise_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_pointwise_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

structure BranchData where
  existsVars : Array Expr
  equations  : Array Expr
  eqForms    : Array ACUEqForm
  matrix     : BranchMatrix

structure CertData where
  premise     : Expr
  premiseForm : ACUEqForm
  branches    : Array BranchData

def buildBranchData
    (premForm : ACUEqForm)
    (existsVars : Array Expr)
    (core : Expr) :
    MetaM BranchData := do
  let conjuncts ← flattenAnd core

  let mut eqForms : Array ACUEqForm := #[]
  for c in conjuncts do
    eqForms := eqForms.push (← normalizeACUEq c)

  let matrix := buildBranchMatrix premForm existsVars eqForms

  pure {
    existsVars := existsVars
    equations := conjuncts
    eqForms := eqForms
    matrix := matrix
  }

def buildCertDataFromTarget (target : Expr) : MetaM CertData := do
  let target ← instantiateMVars target
  let (prem, cert) ← peelImp target
  let premForm ← normalizeACUEq prem
  let branchExprs ← flattenOr cert

  let mut branches : Array BranchData := #[]

  for b in branchExprs do
    let bd ← withPeelExists b #[] fun xs core => do
      buildBranchData premForm xs core
    branches := branches.push bd

  pure {
    premise := prem
    premiseForm := premForm
    branches := branches
  }

def logBranchDataSummary (idx : Nat) (bd : BranchData) : MetaM Unit := do
  logInfo m!"branch {toString idx}:"
  logInfo m!"  exists: {toString bd.existsVars.size}"
  logInfo m!"  equations: {toString bd.equations.size}"
  logInfo m!"  atoms in matrix: {toString bd.matrix.atoms.size}"

  logSignedRow "  premise row" bd.matrix.premise

  let mut i : Nat := 0
  for row in bd.matrix.branchRows do
    logSignedRow s!"  branch row {i}" row
    i := i + 1

elab "acu_cert_data_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"ACU certificate data"
    logInfo m!"number of branches: {toString data.branches.size}"

    let mut i : Nat := 0
    for bd in data.branches do
      logBranchDataSummary i bd
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_data_inspect
  sorry

example (X Y : Multiset Nat) :
    X + Y = ({1} : Multiset Nat) + {2} →
    (X = ({1} : Multiset Nat) + {2} ∧ Y = 0) ∨
    (X = ({1} : Multiset Nat) ∧ Y = {2}) ∨
    (X = ({2} : Multiset Nat) ∧ Y = {1}) ∨
    (X = 0 ∧ Y = ({1} : Multiset Nat) + {2}) := by
  acu_cert_data_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_data_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Build a right-associated conjunction.

Input:

  #[P, Q, R]

Output:

  P ∧ Q ∧ R

The empty conjunction is True.
-/
partial def mkAndAll (props : Array Expr) : MetaM Expr := do
  let mut acc? : Option Expr := none
  for p in props do
    match acc? with
    | none =>
        acc? := some p
    | some acc =>
        let acc' ← mkAppM ``And #[acc, p]
        acc? := some acc'
  match acc? with
  | some acc => pure acc
  | none => pure (mkConst ``True)

/--
Build an implication P → Q.
-/
def mkImpExpr (p q : Expr) : Expr :=
  mkForall `h BinderInfo.default p q

/--
Build nested existential quantifiers over the local Nat witness variables.

Given local variables:

  #[u0, u1, u2]

and body:

  P u0 u1 u2

construct:

  ∃ u0 : Nat, ∃ u1 : Nat, ∃ u2 : Nat, P u0 u1 u2

This uses `mkExistsFVars`, which abstracts the local variables correctly.
-/
def mkExistsOne (v : Expr) (body : Expr) : MetaM Expr := do
  let pred ← mkLambdaFVars #[v] body
  mkAppM ``Exists #[pred]

def mkExistsOver (vars : Array Expr) (body : Expr) : MetaM Expr := do
  let mut out := body
  for v in vars.toList.reverse do
    out ← mkExistsOne v out
  pure out

/--
Build the branch rows as a conjunction of Nat equations, using fresh Nat
variables for existential multiset parameters.
-/
def mkBranchRowsConjunction
    (e : Expr)
    (uVars : Array Expr)
    (rows : Array SignedRow) :
    MetaM Expr := do
  let mut props : Array Expr := #[]
  for row in rows do
    props := props.push (← signedRowToNatEqExprWithEVars e uVars row)
  mkAndAll props

/--
Build the pointwise coverage proposition for one branch:

  premise_row(e) →
  ∃ u0 ... uk,
    branch_rows(e, u0, ..., uk)
-/
def mkPointwiseBranchProp
    (e : Expr)
    (m : BranchMatrix) :
    MetaM Expr := do
  withNatWitnessVars m.existsVars.size #[] fun uVars => do
    let prem ← signedRowToNatEqExprWithEVars e uVars m.premise
    let body ← mkBranchRowsConjunction e uVars m.branchRows
    let existsBody ← mkExistsOver uVars body
    pure (mkImpExpr prem existsBody)

/--
Inspect the generated pointwise branch proposition.
-/
def inspectPointwiseBranchProp (idx : Nat) (m : BranchMatrix) : MetaM Unit := do
  if h : 0 < m.atoms.size then
    let atom0 := m.atoms[0]
    let elemTy ← getElemTypeOfMultisetAtom atom0
    withLocalDeclD `e elemTy fun e => do
      let prop ← mkPointwiseBranchProp e m
      logInfo m!"branch {toString idx}: pointwise coverage proposition"
      logInfo m!"{prop}"
  else
    throwError "Cannot infer element type: branch has no atoms"

/--
Inspector for generated pointwise branch coverage propositions.
-/
elab "acu_cert_pointwise_prop_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"number of branches: {toString data.branches.size}"

    let mut i : Nat := 0
    for bd in data.branches do
      inspectPointwiseBranchProp i bd.matrix
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_pointwise_prop_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_pointwise_prop_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Fixed atom column entry.

For a branch with existential parameters U₀, ..., Uₖ,
each existential parameter induces a vector over the fixed atoms.

Example:

  X = U + V + W
  A = U + U + V
  B = V + W + W

For existential U, the vector is:

  X ↦ 1
  A ↦ 2
  B ↦ 0
-/
structure ColumnEntry where
  fixedAtom : Expr
  coeff     : Nat

abbrev Column := Array ColumnEntry

/--
Return true iff an atom is fixed, not existential.
-/
def isFixedAtom (existsVars : Array Expr) (a : Expr) : Bool :=
  match classifyAtom existsVars a with
  | .fixed => true
  | .existential _ => false

def collectFixedAtomsFromMatrix (m : BranchMatrix) : Array Expr :=
  Id.run do
    let mut out : Array Expr := #[]
    for a in m.atoms do
      if isFixedAtom m.existsVars a then
        out := pushAtomIfMissing out a
    return out

/--
Given a branch matrix and an existential index j, compute how many copies of
that existential parameter occur in the definition of each fixed atom.

This assumes the common MGU-schema orientation where branch rows have shape:

  fixed_atom = ACU expression involving existential params

or, in signed-row form:

  +1 fixed_atom - ... existential terms ... = 0

For each row, if the row has exactly one positive fixed atom, we record
the negative coefficient of existential j as that fixed atom's column entry.
-/
def extractColumnForExistential
    (m : BranchMatrix)
    (j : Nat) :
    MetaM Column := do

  let fixedAtoms := collectFixedAtomsFromMatrix m

  let mut col : Column := #[]

  for fa in fixedAtoms do
    let mut coeff : Nat := 0

    for row in m.branchRows do
      -- Does this row define the fixed atom `fa` with positive coefficient?
      let mut definesFA := false
      for t in row do
        if sameAtom t.atom fa && t.coeff > 0 then
          definesFA := true

      if definesFA then
        for t in row do
          match t.kind with
          | .existential idx =>
              if idx = j && t.coeff < 0 then
                coeff := coeff + Int.toNat (-t.coeff)
          | .fixed =>
              pure ()

    col := col.push { fixedAtom := fa, coeff := coeff }

  pure col

def logColumn (label : String) (col : Column) : MetaM Unit := do
  logInfo m!"{label}:"
  for entry in col do
    logInfo m!"  coeff {toString entry.coeff}: {entry.fixedAtom}"

/--
Inspect the candidate basis columns induced by a branch's existential variables.
-/
def inspectBranchColumns (idx : Nat) (m : BranchMatrix) : MetaM Unit := do
  logInfo m!"branch {toString idx}: candidate columns from existential parameters"

  let fixedAtoms := collectFixedAtomsFromMatrix m
  logInfo m!"  fixed atoms: {toString fixedAtoms.size}"
  for a in fixedAtoms do
    logInfo m!"    {a}"

  let mut j : Nat := 0
  for _u in m.existsVars do
    let col ← extractColumnForExistential m j
    logColumn s!"  existential column {j}" col
    j := j + 1

/--
Generic column inspector.

This extracts the candidate Hilbert-basis / generator columns from each branch.
-/
elab "acu_cert_columns_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"number of branches: {toString data.branches.size}"

    let mut i : Nat := 0
    for bd in data.branches do
      inspectBranchColumns i bd.matrix
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_columns_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_columns_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

def coeffOfAtomInColumn (col : Column) (a : Expr) : Nat :=
  Id.run do
    let mut out : Nat := 0
    for entry in col do
      if sameAtom entry.fixedAtom a then
        out := entry.coeff
    return out

/--
Evaluate a signed premise row on one extracted existential column.

Example premise row:

  2·X - A - B = 0

Column:

  X ↦ 1, A ↦ 2, B ↦ 0

Value:

  2*1 - 1*2 - 1*0 = 0
-/
def evalSignedRowOnColumn (row : SignedRow) (col : Column) : Int :=
  Id.run do
    let mut total : Int := 0
    for t in row do
      match t.kind with
      | .fixed =>
          let c := coeffOfAtomInColumn col t.atom
          total := total + t.coeff * Int.ofNat c
      | .existential _ =>
          -- The premise should not mention branch existentials.
          -- If it does, ignore here; later we should reject such certificates.
          pure ()
    return total

def checkColumnSatisfiesPremise
    (branchIdx : Nat)
    (colIdx : Nat)
    (premise : SignedRow)
    (col : Column) :
    MetaM Unit := do
  let value := evalSignedRowOnColumn premise col
  if value = 0 then
    logInfo m!"branch {toString branchIdx}, column {toString colIdx}: sound, premise evaluates to 0"
  else
    throwError
      "branch {branchIdx}, column {colIdx}: column does not satisfy premise; value = {reprStr value}"

/--
Check all existential columns of one branch against the premise row.
-/
def checkBranchColumnSoundness (branchIdx : Nat) (m : BranchMatrix) : MetaM Unit := do
  let mut j : Nat := 0
  for _u in m.existsVars do
    let col ← extractColumnForExistential m j
    checkColumnSatisfiesPremise branchIdx j m.premise col
    j := j + 1

/--
Generic inspector/checker: each existential column extracted from the schema
must satisfy the premise equation.

This checks that each candidate generator is sound.
-/
elab "acu_cert_column_soundness" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"checking column soundness for {toString data.branches.size} branch(es)"

    let mut i : Nat := 0
    for bd in data.branches do
      checkBranchColumnSoundness i bd.matrix
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_column_soundness
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_column_soundness
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Introduce Nat variables x0, x1, ..., x(n-1).
-/
partial def withNatVars
    {β : Type}
    (pfx : String)
    (n : Nat)
    (acc : Array Expr)
    (k : Array Expr → MetaM β) :
    MetaM β := do
  if acc.size < n then
    let idx := acc.size
    let nm := Name.mkSimple (pfx ++ toString idx)
    withLocalDeclD nm (mkConst ``Nat) fun x => do
      withNatVars pfx n (acc.push x) k
  else
    k acc

def getArrayAtOrThrow
    (xs : Array Expr)
    (i : Nat)
    (msg : String) :
    MetaM Expr := do
  if h : i < xs.size then
    pure xs[i]
  else
    throwError "{msg}: index {toString i}, size {toString xs.size}"

/--
Look up the Nat variable corresponding to a fixed atom.
-/
def lookupFixedNatVar
    (fixedAtoms : Array Expr)
    (xVars : Array Expr)
    (a : Expr) :
    MetaM Expr := do
  match findAtomIndex fixedAtoms a with
  | some i =>
      getArrayAtOrThrow xVars i "fixed variable index out of bounds"
  | none =>
      throwError "Fixed atom was not found in fixed atom basis:\n{a}"

/--
Convert a premise signed row into a Nat equality over abstract fixed variables.

For example, if fixed variables are:

  x0 = count e X
  x1 = count e A
  x2 = count e B

then the row

  2·X - A - B = 0

becomes

  2*x0 = x1 + x2
-/
def signedRowToNatEqOverFixedVars
    (fixedAtoms : Array Expr)
    (xVars : Array Expr)
    (row : SignedRow) :
    MetaM Expr := do
  let mut lhsTerms : Array Expr := #[]
  let mut rhsTerms : Array Expr := #[]

  for t in row do
    match t.kind with
    | .fixed =>
        let base ← lookupFixedNatVar fixedAtoms xVars t.atom

        if t.coeff > 0 then
          let n := Int.toNat t.coeff
          let term ← mkCoeffTimes n base
          lhsTerms := lhsTerms.push term
        else if t.coeff < 0 then
          let n := Int.toNat (-t.coeff)
          let term ← mkCoeffTimes n base
          rhsTerms := rhsTerms.push term
        else
          pure ()

    | .existential _ =>
        throwError
          "Premise row unexpectedly contains an existential atom:\n{t.atom}"

  let lhs ← mkNatSum lhsTerms
  let rhs ← mkNatSum rhsTerms
  mkAppM ``Eq #[lhs, rhs]

/--
Build the linear combination of columns for one fixed atom.

For example, for fixed atom `A` and columns

  U : A ↦ 2
  V : A ↦ 1
  W : A ↦ 0

with coefficient variables c0,c1,c2, this produces:

  2*c0 + c1
-/
def mkColumnCombinationForAtom
    (fa : Expr)
    (cols : Array Column)
    (cVars : Array Expr) :
    MetaM Expr := do
  let mut terms : Array Expr := #[]
  let mut j : Nat := 0

  for col in cols do
    let coeff := coeffOfAtomInColumn col fa
    if coeff ≠ 0 then
      let cVar ← getArrayAtOrThrow cVars j "column coefficient variable index out of bounds"
      let term ← mkCoeffTimes coeff cVar
      terms := terms.push term
    j := j + 1

  mkNatSum terms

/--
Build equations saying that every fixed count variable is generated by the
columns.

For fixed atoms F₀,...,Fₙ and variables x₀,...,xₙ:

  xᵢ = Σⱼ columnⱼ(Fᵢ) * cⱼ
-/
def mkSpanningEquations
    (fixedAtoms : Array Expr)
    (xVars : Array Expr)
    (cols : Array Column)
    (cVars : Array Expr) :
    MetaM Expr := do
  let mut props : Array Expr := #[]
  let mut i : Nat := 0

  for fa in fixedAtoms do
    let x ← getArrayAtOrThrow xVars i "fixed count variable index out of bounds"
    let rhs ← mkColumnCombinationForAtom fa cols cVars
    let eq ← mkAppM ``Eq #[x, rhs]
    props := props.push eq
    i := i + 1

  mkAndAll props

def mkForallOne (v : Expr) (body : Expr) : MetaM Expr := do
  match v with
  | Expr.fvar id =>
      let decl ← id.getDecl
      let body' := body.abstract #[v]
      pure (Expr.forallE decl.userName decl.type body' decl.binderInfo)
  | _ =>
      throwError "Expected free variable for forall binder, got:\n{v}"

def mkForallOver (vars : Array Expr) (body : Expr) : MetaM Expr := do
  let mut out := body
  for v in vars.toList.reverse do
    out ← mkForallOne v out
  pure out

/--
Build the branch spanning proposition.

For a branch with fixed atoms Fᵢ and existential columns Cⱼ:

  premise(Fᵢ-counts) →
  ∃ cⱼ,
    each fixed count is a linear combination of the columns.
-/
def mkBranchSpanningProp (m : BranchMatrix) : MetaM Expr := do
  let fixedAtoms := collectFixedAtomsFromMatrix m

  let mut cols : Array Column := #[]
  let mut j : Nat := 0
  for _u in m.existsVars do
    cols := cols.push (← extractColumnForExistential m j)
    j := j + 1

  withNatVars "x" fixedAtoms.size #[] fun xVars => do
    withNatVars "c" cols.size #[] fun cVars => do
      let prem ← signedRowToNatEqOverFixedVars fixedAtoms xVars m.premise
      let body ← mkSpanningEquations fixedAtoms xVars cols cVars
      let existsBody ← mkExistsOver cVars body
      let imp := mkImpExpr prem existsBody
      mkForallOver xVars imp

def inspectBranchSpanningProp (idx : Nat) (m : BranchMatrix) : MetaM Unit := do
  let prop ← mkBranchSpanningProp m
  logInfo m!"branch {toString idx}: spanning proposition"
  logInfo m!"{prop}"

/--
Inspector for the generated spanning propositions.

This is still inspection-only. It builds the generic arithmetic statement
that must be proved for completeness of an existential branch.
-/
elab "acu_cert_spanning_prop_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"number of branches: {toString data.branches.size}"

    let mut i : Nat := 0
    for bd in data.branches do
      inspectBranchSpanningProp i bd.matrix
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_spanning_prop_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_spanning_prop_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
A generic arithmetic spanning obligation extracted from one branch.

`fixedAtoms` are the original variables/ground multiset atoms.
`columns` are the generator columns extracted from the existential parameters.
`prop` is the closed arithmetic proposition:

  ∀ x0 ... xn,
    premise_row(x0,...,xn) →
    ∃ c0 ... ck,
      x = linear_combination(columns, c)
-/
structure SpanningObligation where
  branchIndex : Nat
  fixedAtoms  : Array Expr
  columns     : Array Column
  prop        : Expr

def buildSpanningObligation
    (branchIndex : Nat)
    (m : BranchMatrix) :
    MetaM SpanningObligation := do

  let fixedAtoms := collectFixedAtomsFromMatrix m

  let mut cols : Array Column := #[]
  let mut j : Nat := 0
  for _u in m.existsVars do
    cols := cols.push (← extractColumnForExistential m j)
    j := j + 1

  let prop ← mkBranchSpanningProp m

  pure {
    branchIndex := branchIndex
    fixedAtoms := fixedAtoms
    columns := cols
    prop := prop
  }

def logSpanningObligation (obl : SpanningObligation) : MetaM Unit := do
  logInfo m!"spanning obligation for branch {toString obl.branchIndex}"
  logInfo m!"fixed atoms: {toString obl.fixedAtoms.size}"

  for a in obl.fixedAtoms do
    logInfo m!"  fixed atom: {a}"

  logInfo m!"columns: {toString obl.columns.size}"

  let mut j : Nat := 0
  for col in obl.columns do
    logColumn s!"  column {j}" col
    j := j + 1

  logInfo m!"proposition:"
  logInfo m!"{obl.prop}"

/--
Build and print all branch spanning obligations.

This is still inspection-only, but it is the correct generic object that the
future prover/checker will consume.
-/
elab "acu_cert_obligations_inspect" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"number of branches: {toString data.branches.size}"

    let mut i : Nat := 0
    for bd in data.branches do
      let obl ← buildSpanningObligation i bd.matrix
      logSpanningObligation obl
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_obligations_inspect
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_obligations_inspect
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Try to prove a closed proposition using `omega`.

This creates a temporary goal of type `prop`, runs `omega`, checks whether
the goal was solved, and then restores the original tactic state.
-/
def tryOmegaOnProp (prop : Expr) : TacticM Bool := do
  let oldGoals ← getGoals

  let mvarExpr ← mkFreshExprMVar (some prop) MetavarKind.syntheticOpaque
  let mvarId := mvarExpr.mvarId!

  setGoals [mvarId]

  try
    evalTactic (← `(tactic| omega))
    let remaining ← getGoals
    setGoals oldGoals
    pure remaining.isEmpty
  catch _ =>
    setGoals oldGoals
    pure false

/--
Try `omega` on one generated spanning obligation.
-/
def tryOmegaOnSpanningObligation (obl : SpanningObligation) : TacticM Unit := do
  logInfo m!"trying omega on spanning obligation for branch {toString obl.branchIndex}"
  logInfo m!"proposition:"
  logInfo m!"{obl.prop}"

  let ok ← tryOmegaOnProp obl.prop

  if ok then
    logInfo m!"omega succeeded for branch {toString obl.branchIndex}"
  else
    logInfo m!"omega failed for branch {toString obl.branchIndex}"

/--
Experimental arithmetic backend.

For each branch, generate the spanning proposition and try to prove it
using `omega`.

This is a backend experiment, not the final certifier.
-/
elab "acu_cert_spanning_omega_try" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"number of branches: {toString data.branches.size}"

    let mut i : Nat := 0
    for bd in data.branches do
      let obl ← buildSpanningObligation i bd.matrix
      tryOmegaOnSpanningObligation obl
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_spanning_omega_try
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_spanning_omega_try
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Result of trying to certify a branch arithmetically.

For now, this is diagnostic. Later `proved` should carry an actual proof
term of the spanning proposition.
-/
inductive ArithBackendResult where
  | proved
  | needsWitnessSynthesis
  | failed (msg : String)
deriving Repr

def arithBackendResultToString : ArithBackendResult → String
  | .proved => "proved"
  | .needsWitnessSynthesis => "needs witness synthesis"
  | .failed msg => "failed: " ++ msg

/--
Temporary arithmetic backend.

Currently:
  - extracts the spanning obligation;
  - tries omega;
  - reports whether witness synthesis is needed.
-/
def diagnoseSpanningObligation
    (obl : SpanningObligation) :
    TacticM ArithBackendResult := do
  let ok ← tryOmegaOnProp obl.prop
  if ok then
    pure .proved
  else
    pure .needsWitnessSynthesis

elab "acu_cert_arith_diagnose" : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    logInfo m!"diagnosing arithmetic backend for {toString data.branches.size} branch(es)"

    let mut i : Nat := 0
    for bd in data.branches do
      let obl ← buildSpanningObligation i bd.matrix
      let result ← diagnoseSpanningObligation obl
      logInfo
        m!"branch {toString i}: {arithBackendResultToString result}"
      i := i + 1

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_arith_diagnose
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_arith_diagnose
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Check that a provided arithmetic theorem proves the generated spanning
obligation for a single-branch certificate.

Usage:

  acu_cert_check_spanning_using my_arith_lemma

This does not prove the original multiset theorem yet.
It only checks that `my_arith_lemma` has exactly the generated arithmetic
spanning proposition as its type.
-/
elab "acu_cert_check_spanning_using " pf:term : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    if hsize : data.branches.size = 1 then
      have h0 : 0 < data.branches.size := by
        omega

      let bd := data.branches[0]

      let obl ← buildSpanningObligation 0 bd.matrix

      let pfExpr ← elabTerm pf none
      let pfType ← inferType pfExpr
      let pfType ← instantiateMVars pfType
      let oblProp ← instantiateMVars obl.prop

      logInfo m!"generated spanning obligation:"
      logInfo m!"{oblProp}"
      logInfo m!"provided proof type:"
      logInfo m!"{pfType}"

      unless (← isDefEq pfType oblProp) do
        throwError
          "provided theorem does not match generated spanning obligation"

      logInfo m!"spanning certificate matches"
    else
      throwError
        "acu_cert_check_spanning_using currently supports exactly one branch; found {toString data.branches.size}"

end ACUCert

namespace ACUCert

lemma span_xy_ab
    (x y a b : Nat)
    (h : x + y = a + b) :
    ∃ c0 c1 c2 c3 : Nat,
      (x = c0 + c2 ∧ y = c1 + c3) ∧
      a = c0 + c1 ∧
      b = c2 + c3 := by
  by_cases hxa : x ≤ a
  · refine ⟨x, a - x, 0, b, ?_⟩
    omega
  · have hax : a ≤ x := Nat.le_of_not_ge hxa
    refine ⟨a, 0, x - a, y, ?_⟩
    omega

lemma span_xy_ab_generated
    (x0 x1 x2 x3 : Nat)
    (h : x0 + x1 = x2 + x3) :
    ∃ c0 c1 c2 c3 : Nat,
      ((x0 = c0 + c2 ∧ x1 = c1 + c3) ∧
        x2 = c0 + c1) ∧
        x3 = c2 + c3 := by
  by_cases hxa : x0 ≤ x2
  · refine ⟨x0, x2 - x0, 0, x3, ?_⟩
    omega
  · have hx2x0 : x2 ≤ x0 := Nat.le_of_not_ge hxa
    refine ⟨x2, 0, x0 - x2, x1, ?_⟩
    omega

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_check_spanning_using ACUCert.span_xy_ab_generated
  sorry

end ACUCert

namespace ACUCert

lemma pointwise_ex2'
    (x y a b : Nat)
    (h : x + y = a + b) :
    ∃ u₁ u₂ u₃ u₄ : Nat,
      x = u₁ + u₃ ∧
      y = u₂ + u₄ ∧
      a = u₁ + u₂ ∧
      b = u₃ + u₄ := by sorry -- from previous file

lemma span_xx_ab_generated
    (x0 x1 x2 : Nat)
    (h : 2 * x0 = x1 + x2) :
    ∃ c0 c1 c2 : Nat,
      ((x0 = c0 + c1 + c2 ∧
        x1 = 2 * c0 + c1) ∧
        x2 = c1 + 2 * c2) := by
  have hx : x0 + x0 = x1 + x2 := by
    omega

  rcases ACUCert.pointwise_ex2' x0 x0 x1 x2 hx with
    ⟨u1, u2, u3, u4, hx13, hx24, hx1, hx2⟩

  by_cases h12 : u1 ≤ u2
  · refine ⟨u1, u2 - u1, u4, ?_⟩
    omega
  · have h21 : u2 ≤ u1 := Nat.le_of_not_ge h12
    refine ⟨u2, u1 - u2, u3, ?_⟩
    omega

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_check_spanning_using ACUCert.span_xx_ab_generated
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

def getCheckedSpanningProofUsing
    (pfSyntax : TSyntax `term)
    (obl : SpanningObligation) :
    TacticM Expr := do
  let pfExpr ← elabTerm pfSyntax none
  let pfType ← inferType pfExpr
  let pfType ← instantiateMVars pfType
  let oblProp ← instantiateMVars obl.prop

  unless (← isDefEq pfType oblProp) do
    throwError
      "provided theorem does not match generated spanning obligation"

  pure pfExpr

elab "acu_cert_check_spanning_using " pf:term : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    if hsize : data.branches.size = 1 then
      have h0 : 0 < data.branches.size := by
        omega

      let bd := data.branches[0]'h0
      let obl ← buildSpanningObligation 0 bd.matrix

      logInfo m!"generated spanning obligation:"
      logInfo m!"{obl.prop}"

      let _pfExpr ← getCheckedSpanningProofUsing pf obl

      logInfo m!"spanning certificate matches"
    else
      throwError
        "acu_cert_check_spanning_using currently supports exactly one branch; found {toString data.branches.size}"

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Instantiate a checked spanning proof at the count values of a fresh element `e`.

If

  pf : ∀ x0 x1 x2 x3,
         x0 + x1 = x2 + x3 →
         ∃ c0 c1 c2 c3, ...

then this logs the type of

  pf (count e X) (count e Y) (count e A) (count e B)

which should be

  count e X + count e Y = count e A + count e B →
    ∃ c0 c1 c2 c3, ...
-/
def inspectSpanningProofAtElement
    (pfExpr : Expr)
    (obl : SpanningObligation) :
    MetaM Unit := do

  if h : 0 < obl.fixedAtoms.size then
    let firstAtom := obl.fixedAtoms[0]'h
    let α ← getElemTypeOfMultisetAtom firstAtom

    withLocalDeclD `e α fun e => do
      let mut countArgs : Array Expr := #[]

      for atom in obl.fixedAtoms do
        let c ← mkCountExpr e atom
        countArgs := countArgs.push c

      let instantiated := mkAppN pfExpr countArgs
      let ty ← inferType instantiated
      let ty ← instantiateMVars ty

      logInfo m!"spanning proof instantiated at a fresh element:"
      logInfo m!"{ty}"
  else
    throwError "cannot instantiate spanning proof: no fixed atoms found"

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

elab "acu_cert_pointwise_using " pf:term : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    if hsize : data.branches.size = 1 then
      have h0 : 0 < data.branches.size := by
        omega

      let bd := data.branches[0]'h0
      let obl ← buildSpanningObligation 0 bd.matrix

      let pfExpr ← getCheckedSpanningProofUsing pf obl

      inspectSpanningProofAtElement pfExpr obl

      logInfo m!"pointwise arithmetic certificate instantiated successfully"
    else
      throwError
        "acu_cert_pointwise_using currently supports exactly one branch; found {toString data.branches.size}"

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_pointwise_using ACUCert.span_xy_ab_generated
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_pointwise_using ACUCert.span_xx_ab_generated
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Try to prove the current pointwise arithmetic premise from the introduced
multiset hypothesis `hACU`, at the fresh element `eACU`.

This is still a generic tactic-level proof:
  - take `congrArg (fun M => count eACU M) hACU`;
  - simplify multiset counts;
  - use omega for linear arithmetic normalization.
-/
def provePointwisePremiseFromH
    (premProp : Expr) :
    TacticM Expr := do
  let oldGoals ← getGoals

  let mvarExpr ← mkFreshExprMVar (some premProp) MetavarKind.syntheticOpaque
  let mvarId := mvarExpr.mvarId!

  setGoals [mvarId]

  let eId : TSyntax `term := mkIdent `eACU
  let hId : TSyntax `term := mkIdent `hACU

  try
    evalTactic (← `(tactic|
      exact by
        have hc := congrArg (fun M => Multiset.count $eId M) $hId
        simpa [
          Multiset.count_add,
          Nat.two_mul,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm
        ] using hc
    ))

    let remaining ← getGoals
    unless remaining.isEmpty do
      setGoals oldGoals
      throwError "failed to close pointwise premise subgoal"

    setGoals oldGoals
    instantiateMVars mvarExpr
  catch ex =>
    setGoals oldGoals
    throw ex

/--
Instantiate the checked spanning proof at counts, then apply it to the
pointwise premise derived from the actual hypothesis `hACU`.
-/
def inspectPointwiseExistenceFromHyp
    (pfExpr : Expr)
    (obl : SpanningObligation)
    (m : BranchMatrix) :
    TacticM Unit := do

  if h : 0 < obl.fixedAtoms.size then
    let firstAtom := obl.fixedAtoms[0]'h
    let α ← getElemTypeOfMultisetAtom firstAtom

    withLocalDeclD `eACU α fun e => do
      let mut countArgs : Array Expr := #[]

      for atom in obl.fixedAtoms do
        let c ← mkCountExpr e atom
        countArgs := countArgs.push c

      let instantiated := mkAppN pfExpr countArgs

      let premProp ← signedRowToNatEqExprWithEVars e #[] m.premise
      let premProof ← provePointwisePremiseFromH premProp

      let existsProof := mkApp instantiated premProof
      let existsType ← inferType existsProof
      let existsType ← instantiateMVars existsType

      logInfo m!"pointwise existential proof obtained from hACU:"
      logInfo m!"{existsType}"
  else
    throwError "cannot instantiate spanning proof: no fixed atoms found"

/--
Introduce the global ACU premise as `hACU`, instantiate the arithmetic
certificate at a fresh element, prove the pointwise premise from `hACU`,
and log the resulting pointwise existential theorem.
-/
elab "acu_cert_pointwise_from_h_using " pf:term : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    if hsize : data.branches.size = 1 then
      have h0 : 0 < data.branches.size := by
        omega

      let bd := data.branches[0]'h0
      let obl ← buildSpanningObligation 0 bd.matrix

      let pfExpr ← getCheckedSpanningProofUsing pf obl

      -- Do not modify the actual goal yet.
      -- Just create a meta-level local hypothesis hACU : data.premise.
      withLocalDeclD `hACU data.premise fun _hACU => do
        inspectPointwiseExistenceFromHyp pfExpr obl bd.matrix

      logInfo m!"successfully derived pointwise existential coefficients from hACU"
    else
      throwError
        "acu_cert_pointwise_from_h_using currently supports exactly one branch; found {toString data.branches.size}"
end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_pointwise_from_h_using ACUCert.span_xy_ab_generated
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_pointwise_from_h_using ACUCert.span_xx_ab_generated
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

/--
Given

  p : ∃ c0 c1 ... c_{n-1}, body

return the witness expressions

  #[c0, c1, ..., c_{n-1}]

obtained by repeated `Classical.choose`, together with the final proof of `body`.
-/
def chooseNestedExists
    (p : Expr)
    (n : Nat) :
    MetaM (Array Expr × Expr) := do
  let mut proof := p
  let mut witnesses : Array Expr := #[]

  for _i in List.range n do
    let w ← mkAppM ``Classical.choose #[proof]
    witnesses := witnesses.push w
    proof ← mkAppM ``Classical.choose_spec #[proof]

  pure (witnesses, proof)

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

def mkPointwiseExistsProofFromHyp
    (pfExpr : Expr)
    (obl : SpanningObligation)
    (m : BranchMatrix)
    (e : Expr) :
    TacticM Expr := do

  let mut countArgs : Array Expr := #[]

  for atom in obl.fixedAtoms do
    let c ← mkCountExpr e atom
    countArgs := countArgs.push c

  let instantiated := mkAppN pfExpr countArgs

  let premProp ← signedRowToNatEqExprWithEVars e #[] m.premise
  let premProof ← provePointwisePremiseFromH premProp

  let existsProof := mkApp instantiated premProof
  instantiateMVars existsProof

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

def inspectChosenCoefficientFunctionsFromHyp
    (pfExpr : Expr)
    (obl : SpanningObligation)
    (m : BranchMatrix) :
    TacticM Unit := do

  if h : 0 < obl.fixedAtoms.size then
    let firstAtom := obl.fixedAtoms[0]'h
    let α ← getElemTypeOfMultisetAtom firstAtom

    withLocalDeclD `eACU α fun e => do
      let existsProof ← mkPointwiseExistsProofFromHyp pfExpr obl m e

      let numCoeffs := obl.columns.size
      let (coeffs, bodyProof) ← chooseNestedExists existsProof numCoeffs

      logInfo m!"chosen pointwise coefficient expressions:"
      let mut i : Nat := 0
      for c in coeffs do
        let cTy ← inferType c
        let cFun ← mkLambdaFVars #[e] c
        let cFunTy ← inferType cFun

        logInfo m!"  coefficient {toString i}:"
        logInfo m!"    pointwise term type: {cTy}"
        logInfo m!"    function type: {cFunTy}"

        i := i + 1

      let bodyTy ← inferType bodyProof
      let bodyTy ← instantiateMVars bodyTy

      logInfo m!"remaining pointwise equations after choosing coefficients:"
      logInfo m!"{bodyTy}"
  else
    throwError "cannot choose coefficient functions: no fixed atoms found"

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

elab "acu_cert_choose_coeffs_using " pf:term : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    if hsize : data.branches.size = 1 then
      have h0 : 0 < data.branches.size := by
        omega

      let bd := data.branches[0]'h0
      let obl ← buildSpanningObligation 0 bd.matrix

      let pfExpr ← getCheckedSpanningProofUsing pf obl

      withLocalDeclD `hACU data.premise fun _hACU => do
        inspectChosenCoefficientFunctionsFromHyp pfExpr obl bd.matrix

      logInfo m!"successfully built coefficient functions from pointwise certificate"
    else
      throwError
        "acu_cert_choose_coeffs_using currently supports exactly one branch; found {toString data.branches.size}"

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_choose_coeffs_using ACUCert.span_xy_ab_generated
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_choose_coeffs_using ACUCert.span_xx_ab_generated
  sorry

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

def mkMultisetSumFromAtoms (atoms : Array Expr) : MetaM Expr := do
  if h : 0 < atoms.size then
    let mut acc := atoms[0]'h
    let mut i : Nat := 1
    while hi : i < atoms.size do
      acc ← mkAppM ``HAdd.hAdd #[acc, atoms[i]]
      i := i + 1
    pure acc
  else
    throwError "cannot build support from empty atom list"

def mkSupportFromFixedAtoms (fixedAtoms : Array Expr) : MetaM Expr := do
  let sum ← mkMultisetSumFromAtoms fixedAtoms
  mkAppM ``Multiset.dedup #[sum]

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

def mkChosenCoefficientFunctionsFromHyp
    (pfExpr : Expr)
    (obl : SpanningObligation)
    (m : BranchMatrix) :
    TacticM (Array Expr) := do

  if h : 0 < obl.fixedAtoms.size then
    let firstAtom := obl.fixedAtoms[0]'h
    let α ← getElemTypeOfMultisetAtom firstAtom

    withLocalDeclD `eACU α fun e => do
      let existsProof ← mkPointwiseExistsProofFromHyp pfExpr obl m e

      let numCoeffs := obl.columns.size
      let (coeffs, _bodyProof) ← chooseNestedExists existsProof numCoeffs

      let mut coeffFuns : Array Expr := #[]

      for c in coeffs do
        let f ← mkLambdaFVars #[e] c
        coeffFuns := coeffFuns.push f

      pure coeffFuns
  else
    throwError "cannot build coefficient functions: no fixed atoms found"

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

variable {α : Type} [DecidableEq α]

def mkWitness (s : Multiset α) (f : α → Nat) : Multiset α :=
  s.bind (fun a => Multiset.replicate (f a) a)

def mkWitnessMultisetsFromCoeffFunctions
    (obl : SpanningObligation)
    (coeffFuns : Array Expr) :
    MetaM (Array Expr) := do

  let support ← mkSupportFromFixedAtoms obl.fixedAtoms

  let mut witnesses : Array Expr := #[]

  for f in coeffFuns do
    let U ← mkAppM ``ACUCert.mkWitness #[support, f]
    witnesses := witnesses.push U

  pure witnesses

def inspectWitnessMultisetsFromHyp
    (pfExpr : Expr)
    (obl : SpanningObligation)
    (m : BranchMatrix) :
    TacticM Unit := do

  let coeffFuns ← mkChosenCoefficientFunctionsFromHyp pfExpr obl m
  let witnesses ← mkWitnessMultisetsFromCoeffFunctions obl coeffFuns

  logInfo m!"constructed candidate witness multisets:"

  let mut i : Nat := 0
  for U in witnesses do
    let ty ← inferType U
    let ty ← instantiateMVars ty

    logInfo m!"  witness {toString i}:"
    logInfo m!"    {U}"
    logInfo m!"    type: {ty}"

    i := i + 1

end ACUCert



namespace ACUCert

open Lean Meta Elab Tactic

elab "acu_cert_build_witnesses_using " pf:term : tactic => do
  withMainContext do
    let target ← getMainTarget
    let data ← buildCertDataFromTarget target

    if hsize : data.branches.size = 1 then
      have h0 : 0 < data.branches.size := by
        omega

      let bd := data.branches[0]'h0
      let obl ← buildSpanningObligation 0 bd.matrix

      let pfExpr ← getCheckedSpanningProofUsing pf obl

      withLocalDeclD `hACU data.premise fun _hACU => do
        inspectWitnessMultisetsFromHyp pfExpr obl bd.matrix

      logInfo m!"successfully constructed candidate witness multisets"
    else
      throwError
        "acu_cert_build_witnesses_using currently supports exactly one branch; found {toString data.branches.size}"

end ACUCert

namespace ACUCert

open Multiset

example (X Y A B : Multiset Nat) :
    X + Y = A + B →
    ∃ U₁ U₂ U₃ U₄ : Multiset Nat,
      X = U₁ + U₃ ∧
      Y = U₂ + U₄ ∧
      A = U₁ + U₂ ∧
      B = U₃ + U₄ := by
  acu_cert_build_witnesses_using ACUCert.span_xy_ab_generated
  sorry

example (X A B : Multiset Nat) :
    X + X = A + B →
    ∃ U V W : Multiset Nat,
      X = U + V + W ∧
      A = U + U + V ∧
      B = V + W + W := by
  acu_cert_build_witnesses_using ACUCert.span_xx_ab_generated
  sorry

end ACUCert
