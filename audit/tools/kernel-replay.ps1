# Replays the declarations of each locally compiled module through the Lean kernel
# using the toolchain's standalone `leanchecker` (olean replay from imports).
$ErrorActionPreference = 'Continue'
$log = 'C:\e338\audit\logs\leanchecker.log'
Push-Location -LiteralPath 'C:\e338\orig'
try { $envLines = & lake env } finally { Pop-Location }
$env:LEAN_PATH = (($envLines | Where-Object { $_ -like 'LEAN_PATH=*' }) -replace '^LEAN_PATH=', '').Trim()
$sysroot = (($envLines | Where-Object { $_ -like 'LEAN_SYSROOT=*' }) -replace '^LEAN_SYSROOT=', '').Trim()
$checker = Join-Path $sysroot 'bin\leanchecker.exe'
$modules = @(
    'MiscYD',
    'FiniteModular', 'BoundedByOrderFixed', 'UniformProgression', 'LemmaThree',
    'DensityPartners', 'CollisionDensity', 'UniformDensity', 'WeightedCount',
    'InfiniteLevels', 'KneserFamily', 'ProgressionFromKneser', 'BoundFromKneser',
    'PaddedProgression', 'PaddedEmbedding', 'SingleSetCovering', 'ProductiveWindow',
    'TwoScale', 'CommonWindows', 'Erdos338Unconditional'
)
Set-Content -Path $log -Value "leanchecker: $checker" -Encoding utf8
$fail = 0
foreach ($m in $modules) {
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $tmp = "C:\e338\audit\logs\leanchecker.$m.tmp"
    cmd /c "`"$checker`" -v $m > `"$tmp`" 2>&1"
    $code = $LASTEXITCODE
    $sw.Stop()
    $line = "[{0}] exit={1} time={2}s" -f $m, $code, [int]$sw.Elapsed.TotalSeconds
    Add-Content -Path $log -Value $line -Encoding utf8
    Get-Content $tmp | Add-Content -Path $log -Encoding utf8
    Remove-Item $tmp
    $line
    if ($code -ne 0) { $fail++ }
}
"modules failing kernel replay: $fail of $($modules.Count)" | Tee-Object -FilePath $log -Append
