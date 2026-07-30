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

$runtime = @(
  "libInit_shared.dll",
  "libLake_shared.dll",
  "libleanshared.dll",
  "libleanshared_1.dll",
  "libleanshared_2.dll"
)

New-Item -ItemType Directory -Force -Path $outputDir | Out-Null
Copy-Item -LiteralPath $exe -Destination $outputDir -Force
$frontendDir = Join-Path $outputDir "Frontend"
New-Item -ItemType Directory -Force -Path $frontendDir | Out-Null
foreach ($asset in @("server.py", "index.html", "app.js", "style.css")) {
  Copy-Item -LiteralPath (Join-Path $root "Frontend/$asset") -Destination $frontendDir -Force
}
foreach ($dll in $runtime) {
  Copy-Item -LiteralPath (Join-Path (Split-Path -Parent $exe) $dll) -Destination $outputDir -Force
}
$sysroot = (& lean --print-prefix).Trim()
[IO.File]::WriteAllText(
  (Join-Path $outputDir "leanreach.sysroot"),
  $sysroot,
  [Text.UTF8Encoding]::new($false)
)

Get-ChildItem -LiteralPath $outputDir | Select-Object Name, Length
