#!/bin/bash

export JAVA_OPTS="-Dfile.encoding=UTF-8"
emacs --no-site-file -q --eval '(set-language-environment "UTF-8")' -l PG/generic/proof-site.el "$@"
