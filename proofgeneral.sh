#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if ! [ -e "$DIR/PG" ]; then
    echo >/dev/stderr "Cannot determine the installation directory that contains the qrhl tool."
    echo >/dev/stderr "Please edit the line 'DIR=...' in proofgeneral.sh, it should set DIR to the installation directory."
    exit 1
fi

chmod +x "$DIR/bin/qrhl" || true
export JAVA_OPTS="-Dfile.encoding=UTF-8"
emacs --no-site-file -q --eval '(set-language-environment "UTF-8")' -l "$DIR/PG/generic/proof-site.el" "$@"
