namespace LeanReach.Cache

/-- A user-visible phase of persistent cache preparation. -/
inductive ProgressPhase where
  | detectingProject
  | preparing
  | readingModules
  | buildingIndex
  | buildingSearch
  | writingSearch
  | buildingQuery
  | writingQuery
  | planningPrettyPrint
  | prettyPrinting
  deriving BEq, Repr

def ProgressPhase.label : ProgressPhase → String
  | .detectingProject => "Detecting project"
  | .preparing => "Preparing cache"
  | .readingModules => "Reading modules"
  | .buildingIndex => "Building index"
  | .buildingSearch => "Building search data"
  | .writingSearch => "Writing search shards"
  | .buildingQuery => "Building query data"
  | .writingQuery => "Writing query shards"
  | .planningPrettyPrint => "Planning pretty-print"
  | .prettyPrinting => "Pretty-printing modules"

/-- A cache progress snapshot. A missing total denotes work whose size is not known yet. -/
structure Progress where
  phase : ProgressPhase
  current : Nat := 0
  total? : Option Nat := none
  detail? : Option String := none
  finished : Bool := false

abbrev ProgressReporter := Progress → IO Unit

def ignoreProgress : ProgressReporter := fun _ => pure ()

/-- Render a Mathlib-style `[current/total]` counter without a trailing newline. -/
def Progress.render (progress : Progress) : String :=
  let total := progress.total?.map toString |>.getD "?"
  let detail := progress.detail?.map (" " ++ ·) |>.getD ""
  s!"[{progress.current}/{total}] {progress.phase.label}{detail}"

structure ProgressDisplay where
  lastUpdate : IO.Ref Nat
  lastLength : IO.Ref Nat
  lastLine : IO.Ref String
  lastPhase : IO.Ref (Option ProgressPhase)

def ProgressDisplay.create : IO ProgressDisplay := do
  return {
    lastUpdate := ← IO.mkRef 0
    lastLength := ← IO.mkRef 0
    lastLine := ← IO.mkRef ""
    lastPhase := ← IO.mkRef none
  }

private def spaces (count : Nat) : String :=
  String.ofList (List.replicate count ' ')

/-- Refresh one progress line on stderr, throttled to Mathlib's ten updates per second. -/
def ProgressDisplay.report (display : ProgressDisplay) : ProgressReporter := fun progress => do
  let now ← IO.monoMsNow
  let lastUpdate ← display.lastUpdate.get
  let lastPhase ← display.lastPhase.get
  let finalCount := progress.total?.any (progress.current ≥ ·)
  unless progress.finished || finalCount || lastPhase != some progress.phase ||
      now - lastUpdate ≥ 100 do
    return
  let line := progress.render
  if line == (← display.lastLine.get) then return
  let previousLength ← display.lastLength.get
  IO.eprint <| "\r" ++ line ++ spaces (previousLength - line.length)
  display.lastUpdate.set now
  display.lastLength.set line.length
  display.lastLine.set line
  display.lastPhase.set (some progress.phase)

/-- Keep the final progress state and terminate its line. -/
def ProgressDisplay.finish (display : ProgressDisplay) : IO Unit := do
  unless (← display.lastLength.get) == 0 do IO.eprint "\n"

end LeanReach.Cache
