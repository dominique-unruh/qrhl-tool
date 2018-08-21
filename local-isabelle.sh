#!/bin/bash

DIR="$(dirname "$(readlink -f "$BASH_SOURCE")")"

if [ "$#" = 0 ]; then
    FILES=("$DIR/isabelle-thys/Test.thy")
else
    FILES=()
fi

/opt/Isabelle2018/bin/isabelle jedit -s -l QRHL-Examples-Prerequisites -d "$DIR" "$@" "$FILES" &
