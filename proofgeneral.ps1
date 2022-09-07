#!/bin/bash

$env:QRHL_PROGRAM_PATH = Join-Path -Path (Resolve-Path -LiteralPath $PSScriptRoot) -ChildPath "bin\qrhl.bat"

$env:JAVA_OPTS="-Dfile.encoding=UTF-8"
emacs "--no-site-file" "-q" "--eval" "(set-variable 'qrhl-prog-name (getenv \`"QRHL_PROGRAM_PATH\`"))" "-l" "proofgeneral/generic/proof-site.el" $args
