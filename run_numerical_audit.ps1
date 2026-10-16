param([string]$JuliaExe = 'julia')
$ErrorActionPreference = 'Stop'
& $JuliaExe --startup-file=no --history-file=no "--project=$PSScriptRoot" (Join-Path $PSScriptRoot 'run_checks.jl')
if ($LASTEXITCODE -ne 0) { throw "Checks failed: $LASTEXITCODE" }
