#!/bin/bash

set -e

SELF="$(readlink -f "$0")"
DIR="$(dirname "$SELF")"

chmod +x "$DIR/bin/qrhl"
export JAVA_OPTS="-Dfile.encoding=UTF-8"
emacs --no-site-file -q --eval '(set-language-environment "UTF-8")' -l "$DIR/PG/generic/proof-site.el" "$@"
