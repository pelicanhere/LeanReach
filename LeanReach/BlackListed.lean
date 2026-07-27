/-
Adapted from Loogle/BlackListed.lean.
Copyright (c) 2019 Robert Y. Lewis and contributors.
Released under the Apache License 2.0.
-/

import Lean

namespace LeanReach

open Lean Meta

/-- Hide generated implementation details while retaining structure projections. -/
def isBlackListed {m} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    (name : Name) : m Bool := do
  let env ← getEnv
  if env.isProjectionFn name then return false
  if (← findDeclarationRanges? name).isNone then return true
  pure name.isInternal
    <||> pure (isAuxRecursor env name)
    <||> pure (isNoConfusion env name)
    <||> pure name.isInternalDetail
    <||> isRec name
    <||> isMatcher name

end LeanReach
