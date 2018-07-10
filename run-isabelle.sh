#!/bin/bash

set -e

SELF="$(readlink -f "$0")"
DIR="$(dirname "$SELF")"

chmod +x "$DIR/bin/qrhl"
"$DIR"/bin/qrhl --isabelle auto "$@"
