#!/bin/bash

$env:QRHL_PROGRAM_PATH = Join-Path -Path (Resolve-Path -LiteralPath $PSScriptRoot) -ChildPath "bin\qrhl.bat"
$PROOFGENERAL_PATH = Join-Path -Path (Resolve-Path -LiteralPath $PSScriptRoot) -ChildPath "proofgeneral\generic\proof-site.el"

$env:JAVA_OPTS="-Dfile.encoding=UTF-8"
emacs "-l" $PROOFGENERAL_PATH "--eval" "(set-variable 'qrhl-prog-name (getenv \`"QRHL_PROGRAM_PATH\`"))" $args
