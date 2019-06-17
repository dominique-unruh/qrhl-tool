#!/bin/bash

set -ex

time /opt/Isabelle2019-RC4/bin/isabelle build -d . QRHL &>minex.log || true

cat minex.log

if grep -F 'exception Match raised (line 338 of "Isar/code.ML")' minex.log; then
    echo "Still an example"
    exit 0
else
    echo "Not an example"
    exit 1
fi
