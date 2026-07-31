import LeanReachMathlibTests.Integration
import Tests.Session
import Tests.Unit

namespace LeanReachMathlibTests

unsafe def main : IO UInt32 := do
  try
    unsafe LeanReach.Tests.Unit.run
    unsafe LeanReach.Tests.Integration.run
    unsafe LeanReach.Tests.SessionTests.run
    IO.println "LeanReach Mathlib tests passed"
    return 0
  catch error =>
    IO.eprintln s!"LeanReach Mathlib tests failed: {error}"
    return 1

end LeanReachMathlibTests

unsafe def main : IO UInt32 :=
  LeanReachMathlibTests.main
