import Lake

open Lake DSL System

package LeanReach where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
  ]

target runtimeDlls pkg : Unit := do
  unless Platform.isWindows do return Job.nil
  let sysroot ← getLeanSysroot
  let dlls : Array FilePath := #[
    "libInit_shared.dll",
    "libLake_shared.dll",
    "libleanshared.dll",
    "libleanshared_1.dll",
    "libleanshared_2.dll",
  ]
  let jobs ← dlls.mapM fun name => do
    let src ← inputBinFile (sysroot / "bin" / name)
    let dst := pkg.binDir / name
    buildFileAfterDep dst src fun src => do
      createParentDirs dst
      copyFile src dst
  return Job.mixArray jobs "runtime DLLs"

@[default_target]
lean_lib LeanReach

lean_lib Tests

@[default_target]
lean_exe leanreach where
  root := `Main
  supportInterpreter := true
  needs := #[runtimeDlls]

lean_exe leanreach_tests where
  root := `Tests.Main
  supportInterpreter := true
  needs := #[runtimeDlls]
