param(
    [double]$Seconds = 900,
    [string]$Cores = '0,1,3,5',
    [int]$Repeats = 1
)
$ErrorActionPreference = 'Stop'
$pythonPath = 'C:\ProgramData\anaconda3\python.exe'
if (-not (Test-Path -LiteralPath $pythonPath)) {
    $pythonCommand = Get-Command python -ErrorAction SilentlyContinue
    if (-not $pythonCommand) {
        throw 'Python was not found. Install Python and NetworkX 3.3, then follow README.md.'
    }
    $pythonPath = $pythonCommand.Source
}
& $pythonPath (Join-Path $PSScriptRoot 'benchmark.py') --seconds $Seconds --cores $Cores --repeats $Repeats
exit $LASTEXITCODE
