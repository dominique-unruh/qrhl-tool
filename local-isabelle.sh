#!/bin/bash

DIR="$(dirname "$(readlink -f "$BASH_SOURCE")")"

/opt/Isabelle2018-RC2/bin/isabelle jedit -s -l QRHL-Examples-Prerequisites -d "$DIR" "$@" &
