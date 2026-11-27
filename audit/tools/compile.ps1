param(
    [Parameter(Mandatory)][string]$Root,      # package root used to derive the module name
    [Parameter(Mandatory)][string]$Module,    # dotted module name, e.g. FormalConjectures.ErdosProblems.338
    [string]$OutDir = 'C:\e338\audit\build',
    [string]$LogDir = 'C:\e338\audit\logs',
    [string]$CandidateDir = 'C:\e338\orig'
)
# Compiles one Lean file with the candidate project's toolchain and LEAN_PATH,
# writing the .olean under $OutDir and the full compiler output under $LogDir.
# Nothing is written into the candidate directory.
$rel = ($Module -replace '\.', '\') + '.lean'
$src = Join-Path $Root $rel
$olean = Join-Path $OutDir (($Module -replace '\.', '\') + '.olean')
$ilean = [System.IO.Path]::ChangeExtension($olean, '.ilean')
New-Item -ItemType Directory -Force -Path (Split-Path $olean), $LogDir | Out-Null
$log = Join-Path $LogDir ($Module + '.log')

Push-Location -LiteralPath $CandidateDir
try {
    $envLines = & lake env
    $leanPath = (($envLines | Where-Object { $_ -like 'LEAN_PATH=*' }) -replace '^LEAN_PATH=', '').Trim()
    $leanExe = (($envLines | Where-Object { $_ -like 'LEAN=*' }) -replace '^LEAN=', '').Trim()
} finally { Pop-Location }
$env:LEAN_PATH = "$OutDir;$leanPath"
$sw = [Diagnostics.Stopwatch]::StartNew()
$cmdline = "`"$leanExe`" `"--root=$Root`" -o `"$olean`" -i `"$ilean`" `"$src`" > `"$log`" 2>&1"
cmd /c $cmdline
$code = $LASTEXITCODE
$sw.Stop()
"[{0}] exit={1} time={2}s lean={3}" -f $Module, $code, [int]$sw.Elapsed.TotalSeconds, $leanExe
exit $code
