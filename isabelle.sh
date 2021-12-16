#!/bin/bash

# Runs a locally installed Isabelle

set -e

#ISABELLE_DIR=~/r/isabelle
ISABELLE_DIR=/opt/Isabelle2021-1

DIR="$(dirname "$BASH_SOURCE[0]")"

if ! [ -e "$DIR/isabelle-thys" ]; then
    echo >/dev/stderr "Cannot determine the installation directory that contains the qrhl tool."
    echo >/dev/stderr "Please edit the line 'DIR=...' in local-isabelle.sh, it should set DIR to the installation directory."
    exit 1
fi

if [ "$#" = 0 ]; then
    FILES=("$DIR/isabelle-thys/All.thy" "$ISABELLE_DIR/src/Pure/ROOT.ML")
else
    FILES=()
fi

#SESSION=QRHL-Examples-Prerequisites
SESSION=Lots-Of-Stuff

"$ISABELLE_DIR"/bin/isabelle jedit -l "$SESSION" -d "$DIR" "$@" "${FILES[@]}" &
