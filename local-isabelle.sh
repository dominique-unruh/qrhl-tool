#!/bin/bash

# Runs a locally installed Isabelle

set -e

ISABELLE_DIR=/opt/Isabelle2018
DIR="$(dirname "$(readlink -f "$BASH_SOURCE")")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/isabelle-thys/Test.thy" "$ISABELLE_DIR/src/Pure/ROOT.ML")
else
    FILES=()
fi

"$ISABELLE_DIR"/bin/isabelle jedit -s -l QRHL-Examples-Prerequisites -d "$DIR" "$@" "${FILES[@]}" &
