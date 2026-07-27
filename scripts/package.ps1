param(
  [string] $Output = ".lake/build/leanreach-dist"
)

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot
$outputDir = [IO.Path]::GetFullPath((Join-Path $root $Output))
$exe = Join-Path $root ".lake/build/bin/leanreach.exe"
if (!(Test-Path -LiteralPath $exe)) {
  throw "Build LeanReach first with 'lake build leanreach'."
}

$sysroot = (& lean --print-prefix).Trim()
$toolchainBin = Join-Path $sysroot "bin"
$runtime = @(
  "libc++.dll",
  "libInit_shared.dll",
  "libLake_shared.dll",
  "libleanshared.dll",
  "libleanshared_1.dll",
  "libleanshared_2.dll",
  "zlib1.dll"
)

New-Item -ItemType Directory -Force -Path $outputDir | Out-Null
Copy-Item -LiteralPath $exe -Destination $outputDir -Force
foreach ($dll in $runtime) {
  Copy-Item -LiteralPath (Join-Path $toolchainBin $dll) -Destination $outputDir -Force
}

Get-ChildItem -LiteralPath $outputDir | Select-Object Name, Length
