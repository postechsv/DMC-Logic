import Lean

open Lean Meta Elab Command Term

-- Recursive helper to walk the AST of a definition
-- and collect all the "leaf" constants joined by ⊔
partial def collectSteps (e : Expr) : MetaM (Array Name) := do
  let fn := e.getAppFn

  -- We strictly look for the native Max.max constant
  if fn.isConstOf ``Max.max then
    let args := e.getAppArgs
    -- Max.max takes 4 arguments: the Type, the Max instance, and the two terms.
    -- We extract and recurse on the last two arguments.
    if args.size >= 4 then
      let left ← collectSteps args[args.size - 2]!
      let right ← collectSteps args[args.size - 1]!
      return left ++ right
    else
      return #[]

  -- Base case: if it's a raw constant (like your individual steps n2w, w2c, etc.)
  else if fn.isConst then
    return #[fn.constName!]

  -- Fallback for any other expression types
  else
    return #[]

-- Define the syntax for the command
syntax (name := printStepsCmd) "#print_steps " ident : command

-- The elaborator that executes the command
@[command_elab printStepsCmd]
def elabPrintSteps : CommandElab := fun stx => do
  match stx with
  | `(command| #print_steps $id) =>
    liftTermElabM do
      let name ← resolveGlobalConstNoOverload id
      let info ← getConstInfo name

      -- Extract the expression tree
      match info.value? with
      | some val =>
        let steps ← collectSteps val
        let stepsFormat := MessageData.joinSep (steps.toList.map toMessageData) m!"\n  "
        logInfo m!"Transition '{name}' is composed of:\n  {stepsFormat}"
      | none =>
        logError m!"'{name}' does not have a computable value."

  | _ => throwUnsupportedSyntax

--#print_steps Step

-- Define the syntax: #apply_steps <Transition> on <Pattern>
syntax (name := applyStepsCmd) "#apply_steps " ident " on " ident : command

@[command_elab applyStepsCmd]
def elabApplySteps : CommandElab := fun stx => do
  match stx with
  | `(command| #apply_steps $transId on $patId) =>
    liftTermElabM do
      -- 1. Resolve the names the user typed
      let transName ← resolveGlobalConstNoOverload transId
      let patName ← resolveGlobalConstNoOverload patId

      let info ← getConstInfo transName

      match info.value? with
      | some val =>
        let steps ← collectSteps val

        -- 2. Iterate through each extracted step
        for stepName in steps do
          -- 3. Construct the exact syntax for a mathematical post-image
          -- fun st' => ∃ st, pat st ∧ step st st'
          let stepIdent := mkIdent stepName
          let patIdent := mkIdent patName
          let termStx ← `(fun st' => ∃ st, $patIdent st ∧ $stepIdent st st')

          try
            -- 4. Ask Lean to elaborate our synthetic syntax into a real Expr
            let expr ← elabTerm termStx none

            -- 5. Reduce the expression (unfold definitions and compute)
            let reducedExpr ← reduce expr

            -- 6. Print the result nicely to the Infoview
            logInfo m!"--- Post-image of {stepName} ---\n{reducedExpr}\n"
          catch e =>
            logError m!"Failed to compute post-image for {stepName}: {e.toMessageData}"

      | none =>
        logError m!"'{transName}' does not have a computable value."

  | _ => throwUnsupportedSyntax
