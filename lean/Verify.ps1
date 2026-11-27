param([switch]$FetchCache)
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    if ($FetchCache) {
        & lake exe cache get
        if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    }

    & lean --version
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    & lake build FiniteModular
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

    $modules = @(
        'BoundedByOrderFixed', 'UniformProgression', 'LemmaThree',
        'DensityPartners', 'CollisionDensity', 'UniformDensity',
        'WeightedCount', 'InfiniteLevels', 'KneserFamily', 'ProgressionFromKneser',
        'BoundFromKneser', 'PaddedProgression', 'PaddedEmbedding',
        'SingleSetCovering', 'ProductiveWindow', 'TwoScale', 'CommonWindows',
        'Erdos338Unconditional'
    )
    foreach ($module in $modules) {
        Write-Host "Checking $module"
        $source = Join-Path $PSScriptRoot "$module.lean"
        $output = Join-Path $PSScriptRoot ".lake/build/lib/lean/$module.olean"
        & lake env lean "--root=$PSScriptRoot" -o $output $source
        if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    }
} finally {
    Pop-Location
}
