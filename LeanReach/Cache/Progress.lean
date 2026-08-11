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

/-- Report a determinate count, marking the phase complete when it reaches its total. -/
def ProgressReporter.count (reporter : ProgressReporter) (phase : ProgressPhase)
    (current total : Nat) (detail? : Option String := none) : IO Unit :=
  reporter {
    phase
    current
    total? := some total
    detail?
    finished := current ≥ total
  }

/-- Render a Mathlib-style `[current/total]` counter without a trailing newline. -/
def Progress.render (progress : Progress) : String :=
  let total := progress.total?.map toString |>.getD "?"
  let detail := progress.detail?.map (" " ++ ·) |>.getD ""
  s!"[{progress.current}/{total}] {progress.phase.label}{detail}"

private structure ProgressDisplayState where
  lastUpdate : Nat := 0
  lastLength : Nat := 0
  lastLine : String := ""
  lastPhase : Option ProgressPhase := none

structure ProgressDisplay where
  state : IO.Ref ProgressDisplayState

def ProgressDisplay.create : IO ProgressDisplay := do
  return { state := ← IO.mkRef {} }

private def spaces (count : Nat) : String :=
  String.ofList (List.replicate count ' ')

/-- Refresh one progress line on stderr, throttled to Mathlib's ten updates per second. -/
def ProgressDisplay.report (display : ProgressDisplay) : ProgressReporter := fun progress => do
  let now ← IO.monoMsNow
  let previous ← display.state.get
  let finalCount := progress.total?.any (progress.current ≥ ·)
  unless progress.finished || finalCount || previous.lastPhase != some progress.phase ||
      now - previous.lastUpdate ≥ 100 do
    return
  let line := progress.render
  if line == previous.lastLine then return
  IO.eprint <| "\r" ++ line ++ spaces (previous.lastLength - line.length)
  display.state.set {
    lastUpdate := now
    lastLength := line.length
    lastLine := line
    lastPhase := some progress.phase
  }

/-- Keep the final progress state and terminate its line. -/
def ProgressDisplay.finish (display : ProgressDisplay) : IO Unit := do
  unless (← display.state.get).lastLength == 0 do IO.eprint "\n"

end LeanReach.Cache
