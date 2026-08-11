namespace LeanReach.Cache

/-- A user-visible phase of persistent cache preparation. -/
inductive ProgressPhase where
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

/-- A cache progress snapshot. A missing total denotes work whose size is not known yet. -/
structure Progress where
  phase : ProgressPhase
  current : Nat := 0
  total? : Option Nat := none
  detail? : Option String := none
  finished : Bool := false

abbrev ProgressReporter := Progress → IO Unit

def ignoreProgress : ProgressReporter := fun _ => pure ()

end LeanReach.Cache
