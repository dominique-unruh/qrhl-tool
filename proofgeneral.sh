#!/bin/bash

set -ex

DIR="$(dirname "${BASH_SOURCE[0]}")"

if ! [ -e "$DIR/proofgeneral" ]; then
    echo >/dev/stderr "Cannot determine the installation directory that contains the qrhl tool."
    echo >/dev/stderr "Please edit the line 'DIR=...' in proofgeneral.sh, it should set DIR to the installation directory."
    exit 1
fi

QRHL_ABS_PATH="$(realpath -L -m "$DIR/bin/qrhl")"

chmod +x "$DIR/bin/qrhl" || true  # Sometimes bin/qrhl does not have the executable bit set after unpacking
export JAVA_OPTS="-Dfile.encoding=UTF-8"
emacs -l "$DIR/proofgeneral/generic/proof-site.el" --eval "(set-variable 'qrhl-prog-name \"$QRHL_ABS_PATH\")" "$@"
