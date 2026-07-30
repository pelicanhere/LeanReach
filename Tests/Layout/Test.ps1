param(
  [string]$LeanReach
)

$ErrorActionPreference = "Stop"
$layoutDir = $PSScriptRoot
$repoDir = Split-Path (Split-Path $layoutDir -Parent) -Parent
$rootDir = Join-Path $layoutDir "Root"
$dependencyDir = Join-Path $layoutDir "Dependency"

function Reset-GeneratedFiles {
  param([string]$ProjectDir)
  $target = [IO.Path]::GetFullPath((Join-Path $ProjectDir ".lake"))
  $allowed = [IO.Path]::GetFullPath($layoutDir).TrimEnd(
    [IO.Path]::DirectorySeparatorChar,
    [IO.Path]::AltDirectorySeparatorChar
  ) + [IO.Path]::DirectorySeparatorChar
  $comparison =
    if ($IsWindows) {
      [StringComparison]::OrdinalIgnoreCase
    } else {
      [StringComparison]::Ordinal
    }
  if (-not $target.StartsWith($allowed, $comparison)) {
    throw "refusing to remove generated files outside '$layoutDir': $target"
  }
  if (Test-Path -LiteralPath $target) {
    Remove-Item -LiteralPath $target -Recurse -Force
  }
}

if (-not $LeanReach) {
  $name = if ($IsWindows) { "leanreach.exe" } else { "leanreach" }
  $LeanReach = Join-Path $repoDir ".lake/build/bin/$name"
}
$LeanReach = (Resolve-Path $LeanReach).Path

function Invoke-Checked {
  param(
    [string]$Command,
    [string[]]$Arguments
  )
  & $Command @Arguments
  if ($LASTEXITCODE -ne 0) {
    throw "'$Command $($Arguments -join ' ')' failed with exit code $LASTEXITCODE"
  }
}

function Read-Query {
  param([string]$Name)
  $output = & $LeanReach $Name --json
  if ($LASTEXITCODE -ne 0) {
    throw "LeanReach failed to query '$Name'"
  }
  return $output | ConvertFrom-Json
}

Reset-GeneratedFiles $rootDir
Reset-GeneratedFiles $dependencyDir

Push-Location $rootDir
try {
  Invoke-Checked lake @("update")
  Invoke-Checked lake @("clean")
  Invoke-Checked lake @("build", "LayoutRoot.Built")

  $rootOlean = Join-Path $rootDir ".lake/root-build/olean/LayoutRoot/Built.olean"
  $unbuiltOlean = Join-Path $rootDir ".lake/root-build/olean/LayoutRoot/Unbuilt.olean"
  $dependencyOlean =
    Join-Path $dependencyDir ".lake/dependency-build/olean/LayoutDependency.olean"
  if (-not (Test-Path $rootOlean) -or -not (Test-Path $dependencyOlean)) {
    throw "Lake did not use the custom build and lean library directories"
  }
  if (Test-Path $unbuiltOlean) {
    throw "the partial build unexpectedly compiled LayoutRoot.Unbuilt"
  }
  $helperOlean = Join-Path $rootDir ".lake/root-build/olean/LayoutRoot/Helper.olean"
  if (-not (Test-Path $helperOlean)) {
    throw "Lake did not build the local module imported outside the configured glob"
  }

  Set-Location (Join-Path $rootDir "source/lean/LayoutRoot")

  $built = Read-Query "LayoutRoot.builtValue"
  if ($built.target.name -ne "LayoutRoot.builtValue" -or
      $built.target.source.file -notlike "*Root*source*lean*LayoutRoot*Built.lean") {
    throw "LeanReach did not detect the built module in its custom source directory"
  }

  $dependency = Read-Query "LayoutDependency.answer"
  if ($dependency.target.name -ne "LayoutDependency.answer" -or
      $dependency.target.source.file -notlike
        "*Dependency*source*lean*LayoutDependency.lean") {
    throw "LeanReach did not detect the path dependency"
  }

  $helper = Read-Query "LayoutRoot.helper"
  if ($helper.target.name -ne "LayoutRoot.helper") {
    throw "LeanReach did not detect the built local module outside the configured glob"
  }

  $unbuilt = & $LeanReach "LayoutRoot.unbuiltValue" --json 2>&1
  if ($LASTEXITCODE -eq 0) {
    throw "LeanReach detected an unbuilt module: $unbuilt"
  }
  if (Test-Path $unbuiltOlean) {
    throw "LeanReach unexpectedly built the unbuilt module"
  }
} finally {
  Pop-Location
}

Write-Output "LeanReach Lake layout test passed"
