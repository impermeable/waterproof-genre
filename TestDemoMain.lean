/-
  Test executable for verifying that WaterproofGenre/Demo.lean elaborates correctly.

  Compile-time checks (verified during build):
  - `hello` is defined and equals "Hello, World!"
  - `test` theorem has type `5 + 5 = 10`
  - The proof term of `test` contains a sub-goal `1 + 2 = 3`
    (from the `have : 1 + 2 = 3 := by sorry` tactic)

  Runtime checks (verified when executed):
  - `#eval hello` produces a "Hello, World!" message
  - The `test` theorem yields a `declaration uses 'sorry'` warning
-/
import WaterproofGenre.Demo

open Lean Elab Meta in

/-! ## Compile-time checks -/

-- Check 1: `hello` evaluates to "Hello, World!"
#guard hello = "Hello, World!"

-- Check 2: `test` has type `5 + 5 = 10` (verifies the main goal)
#check (test : 5 + 5 = 10)

-- Check 3: Inspect the proof term of `test` via metaprogramming.
-- The `have : 1 + 2 = 3 := by sorry` in the proof desugars to a lambda
-- `(fun (this : 1 + 2 = 3) => ...)`. We walk the expression tree to confirm
-- both goals (`5 + 5 = 10` and `1 + 2 = 3`) are present.
open Lean Meta Elab Command in
#eval show MetaM Unit from do
  let env ← getEnv
  let some ci := env.find? `test
    | throwError "'test' not found in environment"

  -- Verify the type pretty-prints as expected (the main goal "5 + 5 = 10")
  let tyStr := toString (← ppExpr ci.type)
  unless (tyStr.splitOn "5 + 5 = 10").length > 1 do
    throwError s!"expected type to contain '5 + 5 = 10', got '{tyStr}'"

  -- Walk the proof expression looking for a lambda binder whose type contains
  -- `1 + 2 = 3`, which corresponds to the `have : 1 + 2 = 3` sub-goal.
  let some val := ci.value?
    | throwError "'test' has no proof term (is it an axiom?)"

  let mut foundSubgoal := false
  -- Use a recursive traversal to walk the Expr tree
  let rec visit (e : Expr) (depth : Nat) : MetaM Bool := do
    if depth == 0 then return false
    match e with
    | .lam _ ty body _ =>
      let tyStr := toString (← ppExpr ty)
      if (tyStr.splitOn "1 + 2 = 3").length > 1 then return true
      let a ← visit ty (depth - 1)
      if a then return true
      visit body (depth - 1)
    | .letE _ ty val body _ =>
      let tyStr := toString (← ppExpr ty)
      if (tyStr.splitOn "1 + 2 = 3").length > 1 then return true
      let a ← visit ty (depth - 1)
      if a then return true
      let b ← visit val (depth - 1)
      if b then return true
      visit body (depth - 1)
    | .app f a =>
      let fa ← visit f (depth - 1)
      if fa then return true
      visit a (depth - 1)
    | .mdata _ e => visit e (depth - 1)
    | .proj _ _ e => visit e (depth - 1)
    | _ => return false
  foundSubgoal ← visit val 100

  unless foundSubgoal do
    throwError s!"expected to find sub-goal '1 + 2 = 3' in the proof term of 'test'"

  logInfo "Compile-time check passed: goals '5 + 5 = 10' and '1 + 2 = 3' confirmed in 'test'"

/-! ## Runtime checks -/

/-- Check whether `sub` occurs as a substring of `s`. -/
private def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def main : IO UInt32 := do
  -- Elaborate Demo.lean in a subprocess and capture diagnostics.
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "WaterproofGenre/Demo.lean"]
  }
  let output := result.stdout ++ result.stderr

  let mut failed := false

  -- Check that #eval hello produces "Hello, World!"
  unless hasSubstr output "Hello, World!" do
    IO.eprintln "FAIL: expected 'Hello, World!' in output from #eval hello"
    IO.eprintln s!"  output was: {output}"
    failed := true

  -- Check that the sorry warning is present
  unless hasSubstr output "declaration uses 'sorry'" do
    IO.eprintln "FAIL: expected 'declaration uses 'sorry'' warning in output"
    IO.eprintln s!"  output was: {output}"
    failed := true

  if failed then
    IO.eprintln "Some Demo.lean elaboration checks failed."
    return 1

  IO.println "All Demo.lean elaboration checks passed!"
  return 0
