/-
Adapted from Loogle/BlackListed.lean.
Copyright (c) 2019 Robert Y. Lewis and contributors.
Released under the Apache License 2.0.
-/

import Lean

namespace LeanReach

open Lean

/-- Hide generated implementation details that can still have source ranges. -/
def isBlackListed (name : Name) : Bool :=
  name.isInternal || name.isInternalDetail || isPrivateName name

end LeanReach
