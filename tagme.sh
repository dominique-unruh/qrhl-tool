#!/bin/bash

if [ "`git status -s -uno`" = "" ]; then
    exit 1
fi

git commit -a -m "`git status -s`"
git tag minex-do-me-$RANDOM
git tag -l | wc
