#!/bin/bash

DIR="$(dirname "$(readlink -f "$BASH_SOURCE")")"

#/opt/Isabelle2018-RC1/bin/isabelle jedit -s -R QRHL-Tests -A QRHL-Prerequisites -d "$DIR"/src/test/isabelle/ "$@" &

/opt/Isabelle2018-RC1/bin/isabelle jedit -s -l QRHL-Examples-Prerequisites -d "$DIR"/src/test/isabelle/ "$@" &
