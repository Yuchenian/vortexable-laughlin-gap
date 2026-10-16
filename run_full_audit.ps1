param(
    [string]$JuliaExe = 'julia',
    [string]$PythonExe = 'python',
    [switch]$SkipReferenceCertificate
)
$ErrorActionPreference = 'Stop'
& $JuliaExe --startup-file=no --history-file=no "--project=$PSScriptRoot" (Join-Path $PSScriptRoot 'run_checks.jl')
if ($LASTEXITCODE -ne 0) { throw "Julia checks failed: $LASTEXITCODE" }
if (-not $SkipReferenceCertificate) {
    & $PythonExe (Join-Path $PSScriptRoot 'scripts/fetch_reference.py') --verify
    if ($LASTEXITCODE -ne 0) { throw "Reference verification failed: $LASTEXITCODE" }
}
