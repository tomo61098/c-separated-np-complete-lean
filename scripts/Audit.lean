import Lean

/-!
Local preflight: compare the independently elaborated Challenge and Solution
statement and every project definition in the Challenge, then audit proof axioms.
This is an additional check, not a replacement for Comparator and NanoDa replay.
Run after `lake build` with `lake env lean --run scripts/Audit.lean`.
-/

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{ module := `Challenge }] {}
  enableInitializersExecution
  let solution ← importModules #[{ module := `Solution }] {} (loadExts := true)
  let target := `CSeparatedNPComplete.partition_gadget_schedule_partition_iff
  let some challengeTheorem := challenge.find? target
    | throw <| IO.userError "Main theorem missing from Challenge"
  let some solutionTheorem := solution.find? target
    | throw <| IO.userError "Main theorem missing from Solution"
  unless challengeTheorem.type == solutionTheorem.type &&
      challengeTheorem.levelParams == solutionTheorem.levelParams do
    throw <| IO.userError "Challenge and Solution theorem types differ"
  let mut count := 0
  for (name, info) in challenge.constants.toList do
    if (`CSeparatedNPComplete).isPrefixOf name && name != target then
      let some other := solution.find? name
        | throw <| IO.userError s!"Solution is missing {name}"
      unless info.type == other.type && info.levelParams == other.levelParams do
        throw <| IO.userError s!"Declaration type differs: {name}"
      if let .defnInfo value := info then
        let .defnInfo otherValue := other
          | throw <| IO.userError s!"Solution declaration is not a definition: {name}"
        unless value.value == otherValue.value do
          throw <| IO.userError s!"Definition body differs: {name}"
        count := count + 1
  let (axioms, _) ← (collectAxioms target : CoreM (Array Name)).toIO
    { fileName := "scripts/Audit.lean", fileMap := default } { env := solution }
  let permitted := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in axioms do
    unless permitted.contains axiomName do
      throw <| IO.userError s!"Forbidden proof dependency: {axiomName}"
  if solution.header.moduleNames.contains `Challenge then
    throw <| IO.userError "Solution imports Challenge"
  IO.println s!"PASS: main theorem types match; {count} definition bodies match."
  IO.println s!"PASS: Solution is independent of Challenge; proof axioms: {axioms}"
