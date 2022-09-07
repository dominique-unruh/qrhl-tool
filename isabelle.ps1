# Isabelle session for editing
$session = "QRHL-Prerequisites"

if ($args.Count -eq 0) {
    $args = ("$PSScriptRoot\isabelle-thys\All.thy")
}
Set-Location $PSScriptRoot
bin\qrhl.ps1 --isabelle --session $session $args
