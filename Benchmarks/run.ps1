param(
  [int] $Iterations = 5,
  [string] $Output = "Benchmarks/latest.csv",
  [switch] $AppendHistory
)

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot
$leanreach = Join-Path $root ".lake/build/leanreach-dist/leanreach.exe"
$mathlib = Join-Path $root ".lake/packages/mathlib/Mathlib"
$queries = @("span_le", "continuous_mul", "tendsto_nat_nhds_top_iff")

if (!(Test-Path -LiteralPath $leanreach)) {
  throw "Create the packaged executable with 'pwsh scripts/package.ps1'."
}

function Get-Median([double[]] $Values) {
  $sorted = $Values | Sort-Object
  $middle = [int] [math]::Floor($sorted.Count / 2)
  if ($sorted.Count % 2) { return $sorted[$middle] }
  return ($sorted[$middle - 1] + $sorted[$middle]) / 2
}

function Measure-LeanReach([string] $Query) {
  $watch = [Diagnostics.Stopwatch]::StartNew()
  $output = & $leanreach search $Query --limit 10 --json --profile 2>&1
  $watch.Stop()
  if ($LASTEXITCODE) { throw "LeanReach failed for '$Query': $output" }
  $profile = $output | Where-Object { $_ -match "query=(\d+)ms" } | Select-Object -Last 1
  if (!$profile -or $profile.ToString() -notmatch "query=(\d+)ms") {
    throw "LeanReach did not report query time for '$Query'."
  }
  [PSCustomObject]@{
    EndToEndMs = $watch.Elapsed.TotalMilliseconds
    QueryMs = [double] $Matches[1]
  }
}

function Measure-Rg([string] $Query) {
  $watch = [Diagnostics.Stopwatch]::StartNew()
  & rg -n --glob "*.lean" $Query $mathlib | Out-Null
  $watch.Stop()
  if ($LASTEXITCODE -gt 1) { throw "rg failed for '$Query'." }
  return $watch.Elapsed.TotalMilliseconds
}

$rows = @()
foreach ($query in $queries) {
  Measure-LeanReach $query | Out-Null
  Measure-Rg $query | Out-Null
  $leanreachEndToEnd = @()
  $leanreachQuery = @()
  $rgEndToEnd = @()
  1..$Iterations | ForEach-Object {
    $sample = Measure-LeanReach $query
    $leanreachEndToEnd += $sample.EndToEndMs
    $leanreachQuery += $sample.QueryMs
    $rgEndToEnd += Measure-Rg $query
  }
  $rows += [PSCustomObject]@{
    Query = $query
    LeanReachEndToEndMs = [math]::Round((Get-Median $leanreachEndToEnd), 2)
    LeanReachQueryMs = [math]::Round((Get-Median $leanreachQuery), 2)
    RgEndToEndMs = [math]::Round((Get-Median $rgEndToEnd), 2)
    Iterations = $Iterations
  }
}

$outputPath = [IO.Path]::GetFullPath((Join-Path $root $Output))
$rows | Export-Csv -LiteralPath $outputPath -NoTypeInformation
$rows | Format-Table -AutoSize

if ($AppendHistory) {
  $commit = (& git -C $root rev-parse --short HEAD).Trim()
  $date = Get-Date -Format "yyyy-MM-dd"
  $history = foreach ($row in $rows) {
    [PSCustomObject]@{
      commit = $commit
      date = $date
      query = $row.Query
      tool = "leanreach"
      metric = "end_to_end"
      median_ms = $row.LeanReachEndToEndMs
      iterations = $row.Iterations
      note = "packaged executable"
    }
    [PSCustomObject]@{
      commit = $commit
      date = $date
      query = $row.Query
      tool = "leanreach"
      metric = "query"
      median_ms = $row.LeanReachQueryMs
      iterations = $row.Iterations
      note = "CLI profile"
    }
    [PSCustomObject]@{
      commit = $commit
      date = $date
      query = $row.Query
      tool = "rg"
      metric = "end_to_end"
      median_ms = $row.RgEndToEndMs
      iterations = $row.Iterations
      note = "warm filesystem"
    }
  }
  $history | Export-Csv -LiteralPath (Join-Path $PSScriptRoot "history.csv") -Append -NoTypeInformation
}
