import Tests.Integration
import Tests.Session
import Tests.Unit

namespace LeanReach.Tests

unsafe def main : IO UInt32 := do
  try
    unsafe Unit.run
    unsafe Integration.run
    unsafe SessionTests.run
    IO.println "LeanReach tests passed"
    return 0
  catch error =>
    IO.eprintln s!"LeanReach tests failed: {error}"
    return 1

end LeanReach.Tests

unsafe def main : IO UInt32 :=
  LeanReach.Tests.main
