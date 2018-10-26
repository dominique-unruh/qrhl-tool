#!/bin/bash

# Runs a locally installed Isabelle

set -e

ISABELLE_DIR=/opt/Isabelle2018

DIR="$(dirname "$BASH_SOURCE[0]")"

if ! [ -e "$DIR/isabelle-thys" ]; then
    echo >/dev/stderr "Cannot determine the installation directory that contains the qrhl tool."
    echo >/dev/stderr "Please edit the line 'DIR=...' in proofgeneral.sh, it should set DIR to the installation directory."
    exit 1
fi

if [ "$#" = 0 ]; then
    FILES=("$DIR/isabelle-thys/Test.thy" "$ISABELLE_DIR/src/Pure/ROOT.ML")
else
    FILES=()
fi

"$ISABELLE_DIR"/bin/isabelle jedit -s -l QRHL-Examples-Prerequisites -d "$DIR" "$@" "${FILES[@]}" &
