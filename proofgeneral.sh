#!/bin/bash

set -e

DIR="$(dirname "$BASH_SOURCE[0]")"

if ! [ -e "$DIR/proofgeneral" ]; then
    echo >/dev/stderr "Cannot determine the installation directory that contains the qrhl tool."
    echo >/dev/stderr "Please edit the line 'DIR=...' in proofgeneral.sh, it should set DIR to the installation directory."
    exit 1
fi

QRHL_ABS_PATH="$(realpath -L -m "$DIR/bin/qrhl")"

chmod +x "$DIR/bin/qrhl" || true
export JAVA_OPTS="-Dfile.encoding=UTF-8"
emacs --no-site-file -q --eval "(set-variable 'qrhl-prog-name \"$QRHL_ABS_PATH\")" -l "$DIR/proofgeneral/generic/proof-site.el" "$@"
