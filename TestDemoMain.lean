/-
  Test executable for verifying that WaterproofGenre/Demo.lean elaborates correctly.

  Compile-time checks (verified during build):
  - `hello` is defined and equals "Hello, World!"
  - `test` theorem has type `5 + 5 = 10`
  - The proof structure includes a subgoal `1 + 2 = 3`

  Runtime checks (verified when executed):
  - `#eval hello` produces a "Hello, World!" message
  - The `test` theorem yields a `declaration uses 'sorry'` warning
-/
import WaterproofGenre.Demo

/-! ## Compile-time checks -/

-- Check 1: `hello` evaluates to "Hello, World!"
#guard hello = "Hello, World!"

-- Check 2: `test` has type `5 + 5 = 10` (verifies the main goal)
#check (test : 5 + 5 = 10)

/-! ## Runtime checks -/

/-- Check whether `sub` occurs as a substring of `s`. -/
private def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def main : IO UInt32 := do
  -- Elaborate Demo.lean in a subprocess and capture diagnostics.
  -- All Lean messages (info + warnings) appear on stdout for this file
  -- because the embedded code blocks are elaborated via processString which
  -- forwards messages through the Verso DocElabM monad.
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

  -- Check that the goal 5 + 5 = 10 appears in the elaboration output.
  -- The processString function traces the code being elaborated, which
  -- includes "theorem test : 5 + 5 = 10 := by", confirming this goal
  -- is present at the correct point in the document.
  unless hasSubstr output "5 + 5 = 10" do
    IO.eprintln "FAIL: expected '5 + 5 = 10' goal in elaboration output"
    IO.eprintln s!"  output was: {output}"
    failed := true

  -- Check that the sub-goal 1 + 2 = 3 appears in the elaboration output.
  -- The processed code includes "have : 1 + 2 = 3 := by", confirming
  -- this sub-goal is present at the correct point in the document.
  unless hasSubstr output "1 + 2 = 3" do
    IO.eprintln "FAIL: expected '1 + 2 = 3' sub-goal in elaboration output"
    IO.eprintln s!"  output was: {output}"
    failed := true

  if failed then
    IO.eprintln "Some Demo.lean elaboration checks failed."
    return 1

  IO.println "All Demo.lean elaboration checks passed!"
  return 0
