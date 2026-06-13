/-
Objective: Maude-based certification generation
-/
import Lean
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

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
    match equations with
    | [] => "True"
    | es => String.intercalate " ∧ " es

  if existVars.isEmpty then
    body
  else
    "∃ (" ++ String.intercalate " " existVars ++ " : Multiset Nat), " ++ body

def parseMaudeUnifiers (us : List String) : String :=
  match us.map (fun u => "(" ++ parseMaudeUnifier u ++ ")") with
  | [] => "False"
  | branches => String.intercalate " ∨ " branches

-- #eval do IO.println <| parseMaudeUnifiers (← getMaudeUnifiers "theory/multiset.maude" query1)
-- #eval do IO.println <| parseMaudeUnifiers (← getMaudeUnifiers "theory/multiset.maude" query2)
-- #eval do IO.println <| parseMaudeUnifiers (← getMaudeUnifiers "theory/multiset.maude" query3)

open Lean Elab Term Meta

private def elabStringValue (stx : Syntax) : TermElabM String := do
  let e ← elabTerm stx (some (mkConst ``String))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e

  let e ← withTransparency .all <| reduce e

  match e with
  | Expr.lit (Literal.strVal s) => pure s
  | _ =>
      throwError "expected a reducible String literal, got:\n{e}"

syntax "maude_unifiers_prop_from" "(" term ", " term ")" : term

elab_rules : term
  | `(maude_unifiers_prop_from($fileTerm, $queryTerm)) => do
      let file ← elabStringValue fileTerm
      let query ← elabStringValue queryTerm

      let us ←
        MonadLiftT.monadLift
          (getMaudeUnifiers file query : IO (List String))

      let code := parseMaudeUnifiers us
      logInfo m!"Generated Maude proposition:\n{code}"

      let env ← getEnv
      match Parser.runParserCategory env `term code with
      | .error err =>
          throwError "failed to parse generated proposition:\n{err}\n\nGenerated code:\n{code}"
      | .ok stx =>
          elabTerm stx (some (mkSort levelZero))

def query1 := "variant unify {3} =? {1} + {2} ."
def query2 := "variant unify X:MSet + Y:MSet =? {1} + {2} ."
def query3 := "variant unify X:MSet + X:MSet =? A:MSet + B:MSet ."
def query4 := "variant unify X:MSet + Y:MSet + {2} =? {1} + Z:MSet ."


-- #eval do getMaudeUnifiers "theory/multiset.maude" query1
-- #eval do getMaudeUnifiers "theory/multiset.maude" query2
-- #eval do getMaudeUnifiers "theory/multiset.maude" query3
#eval do getMaudeUnifiers "theory/multiset.maude" query4

-- example :
--     ({3} : Multiset Nat) = {1} + {2} →
--     maude_unifiers_prop_from("theory/multiset.maude", query1) := by
--   sorry

-- example (X Y : Multiset Nat) :
--     X + Y = {1} + {2} →
--     maude_unifiers_prop_from("theory/multiset.maude", query2) := by
--   sorry

-- example (X Y A B : Multiset Nat) :
--     X + Y = A + B →
--     maude_unifiers_prop_from("theory/multiset.maude", query3) := by
--   sorry

-- proof-by-chatgpt
example (X Y Z : Multiset Nat) :
    X + Y + {2} = {1} + Z →
    maude_unifiers_prop_from("theory/multiset.maude", query4) := by
  intro h

  have hc :
      ∀ a : ℕ,
        X.count a + Y.count a + (if a = 2 then 1 else 0)
          =
        (if a = 1 then 1 else 0) + Z.count a := by
    intro a
    have hcnt := congr_arg (fun M : Multiset ℕ => M.count a) h
    simp [Multiset.count_add, Multiset.count_singleton, Multiset.count_cons] at hcnt
    omega

  by_cases hx : 1 ∈ X

  · left

    have hxpos : 0 < X.count 1 := by
      exact Multiset.count_pos.mpr hx

    refine ⟨X.erase 1, Y, ?_, rfl, ?_⟩

    · ext a
      by_cases ha : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hxpos]
        omega
      · simp [Multiset.count_add, Multiset.count_singleton, ha]

    · ext a
      have hca := hc a
      by_cases ha1 : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hxpos] at hca ⊢
        omega
      · by_cases ha2 : a = 2
        · subst a
          have h21 : (2 : ℕ) ≠ 1 := by decide
          simp [Multiset.count_add, Multiset.count_singleton, h21] at hca ⊢
          omega
        · simp [Multiset.count_add, Multiset.count_singleton, ha1, ha2] at hca ⊢
          omega

  · right

    have hx0 : X.count 1 = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hxpos
      exact hx (Multiset.count_pos.mp hxpos)

    have hypos : 0 < Y.count 1 := by
      have hca := hc 1
      simp [Multiset.count_add, Multiset.count_singleton, hx0] at hca
      omega

    refine ⟨X, Y.erase 1, rfl, ?_, ?_⟩

    · ext a
      by_cases ha : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hypos]
        omega
      · simp [Multiset.count_add, Multiset.count_singleton, ha]

    · ext a
      have hca := hc a
      by_cases ha1 : a = 1
      · subst a
        simp [Multiset.count_add, Multiset.count_singleton, hx0, hypos] at hca ⊢
        omega
      · by_cases ha2 : a = 2
        · subst a
          have h21 : (2 : ℕ) ≠ 1 := by decide
          simp [Multiset.count_add, Multiset.count_singleton, h21] at hca ⊢
          omega
        · simp [Multiset.count_add, Multiset.count_singleton, ha1, ha2] at hca ⊢
          omega
