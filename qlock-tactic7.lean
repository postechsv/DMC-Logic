/-
Objective: Maude-based certification generation
-/
import Lean

open Lean Elab Command

def getMaudeUnifiers (filename : String) (query : String) : IO (List String) := do
  IO.FS.withTempFile fun h queryPath => do
    h.putStr (query ++ "\n")
    h.flush

    -- Equivalent to: cat (queryPath) | maude (theory.maude)
    let out ← IO.Process.output {
      cmd := "bash"
      args := #[
        "-lc",
        -- $1 is the temporary filename.
        s!"cat \"$1\" | maude -no-banner {filename}",
        "bash",
        queryPath.toString
      ]
    }

    if out.exitCode == 0 then pure (
      out.stdout.splitOn "\n\n" |>.filterMap fun block =>
        let block := block.trim
        if block.startsWith "Unifier " then
          match block.splitOn "\n" with
          | _unifierHeader :: _rewrites :: body =>
              some (String.intercalate "\n" body |>.trim)
          | _ => none
        else
          none)
    else
      throw <| IO.userError
        s!"Maude failed with exit code {out.exitCode}\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}"


syntax "#test_maude_unify " str " with " str : command

elab_rules : command
  | `(#test_maude_unify $filename:str with $query:str) => do
      let stdout ← liftIO <|
        getMaudeUnifiers filename.getString query.getString
      logInfo m!"Maude unifiers:\n{stdout}"

#test_maude_unify "theory/multiset.maude" with
  "variant unify {3} =? {1} + {2} ."

#test_maude_unify "theory/multiset.maude" with
  "variant unify X:MSet + Y:MSet =? {1} + {2} ."

#test_maude_unify "theory/multiset.maude" with
  "variant unify X:MSet + X:MSet =? A:MSet + B:MSet ."


def parseMaudeUnifier (u : String) : String :=
  let stripSort (s : String) : String :=
    match s.trim.splitOn ":" with
    | x :: _ => x.trim
    | [] => s.trim

  let maudeExistVar? (s : String) : Option String :=
    let x := stripSort s
    if x.startsWith "%" then
      some ("U" ++ x.drop 1)
    else
      none

  let maudeAtomToLean (s : String) : String :=
    let x := stripSort s
    if x.startsWith "%" then
      "U" ++ x.drop 1
    else if x == "mt" then
      "∅"
    else if x.toNat?.isSome then
      "{" ++ x ++ "}"
    else
      x

  let maudeTermToLean (s : String) : String :=
    s.splitOn "+"
      |>.map maudeAtomToLean
      |> String.intercalate " + "

  let parseMaudeMapping? (line : String) : Option (String × String) :=
    match line.splitOn "-->" with
    | lhs :: rhs :: [] => some (lhs.trim, rhs.trim)
    | _ => none

  let varsInMaudeTerm (s : String) : List String :=
    s.splitOn "+"
      |>.filterMap maudeExistVar?

  let uniqueStrings (xs : List String) : List String :=
    xs.foldl
      (fun acc x => if acc.contains x then acc else acc ++ [x])
      []

  let mappings :=
    u.splitOn "\n"
      |>.filterMap parseMaudeMapping?

  let existVars :=
    mappings
      |>.flatMap (fun (_, rhs) => varsInMaudeTerm rhs)
      |> uniqueStrings

  let equations :=
    mappings.map fun (lhs, rhs) =>
      maudeAtomToLean lhs ++ " = " ++ maudeTermToLean rhs

  let body :=
    String.intercalate " ∧ " equations

  if existVars.isEmpty then
    body
  else
    "∃ " ++ String.intercalate " " existVars ++ ", " ++ body
    --"∃ (" ++ String.intercalate " " existVars ++ " : " ++ "Multiset Nat" ++ "), " ++ body



def getUnifiers
    (lemmaName : String)
    (binders : String)
    (premise : String)
    (filename : String)
    (query : String) : IO String := do
  let us ← getMaudeUnifiers filename query

  let conclusion :=
    match us.map (fun u => "(" ++ parseMaudeUnifier u ++ ")") with
    | [] => "False"
    | branches => String.intercalate " ∨ " branches

  pure s!"lemma {lemmaName} {binders} : {premise} → {conclusion} := by\n  sorry"

#eval do
  IO.println <|
    ← getUnifiers
      "completeness"
      "(X A B : Multiset ℕ)"
      "X + X = A + B"
      "theory/multiset.maude"
      "variant unify X:MSet + X:MSet =? A:MSet + B:MSet ."

-- #eval getUnifiers "theory/multiset.maude"
--       "variant unify X:MSet + X:MSet =? A:MSet + B:MSet ."

-- #eval getUnifiers "theory/multiset.maude"
--       "variant unify X:MSet + Y:MSet =? {1} + {2} ."

-- #eval getUnifiers "theory/multiset.maude"
--       "variant unify {3} =? {1} + {2} ."
