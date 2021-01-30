#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if ! [ -e "$DIR/proofgeneral" ]; then
    echo >/dev/stderr "Cannot determine the installation directory that contains the qrhl tool."
    echo >/dev/stderr "Please edit the line 'DIR=...' in run-isabelle.sh, it should set DIR to the installation directory."
    exit 1
fi

chmod +x "$DIR/bin/qrhl"
"$DIR"/bin/qrhl --isabelle "$@"
