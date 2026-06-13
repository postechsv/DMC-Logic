/-
Objective: Maude-based certification generation
-/
import Lean

open Lean Elab Command

def runMaudeUnifyQuery (filename : String) (query : String) : IO (List String) := do
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
        runMaudeUnifyQuery filename.getString query.getString
      logInfo m!"Maude stdout:\n{stdout}"

#test_maude_unify "tmp/multiset.maude" with
  "variant unify X:MSet + Y:MSet =? 1 + 2 ."

#test_maude_unify "tmp/multiset.maude" with
  "variant unify X:MSet + X:MSet =? A:MSet + B:MSet ."
