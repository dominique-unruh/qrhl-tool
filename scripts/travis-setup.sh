#!/bin/bash

set -ex

TIME_LIMIT=2700

date +%s > ~/start-time

# To avoid Travis killing our job
# Since we have "set -e", this writes "sleep 300" every five minutes
while true; do sleep 300; done &

mkdir -p ~/bin
if ! [ -e ~/install/sbt ]; then
  curl -Ls https://git.io/sbt > ~/install/sbt
fi
chmod +x ~/install/sbt

mkdir -p ~/install
if ! [ -e ~/install/Isabelle2019 ]; then
  case "$TRAVIS_OS_NAME" in
    linux) curl https://isabelle.in.tum.de/website-Isabelle2019/dist/Isabelle2019_linux.tar.gz | tar -x -z -C ~/install;;
    osx) curl https://isabelle.in.tum.de/website-Isabelle2019/dist/Isabelle2019_macos.tar.gz | tar -x -z -C ~/install;;
    *) echo "Unsupported OS: $TRAVIS_OS_NAME"; exit 1;;
  esac
fi

case "$TRAVIS_OS_NAME" in
  linux) ISABELLE_HOME=~/install/Isabelle2019;;
  osx) ISABELLE_HOME=~/install/Isabelle2019.app/Isabelle;;
  *) echo "Unsupported OS: $TRAVIS_OS_NAME"; exit 1;;
esac

mkdir -p ~/install/afp-2019
if ! [ -e ~/install/afp-2019/thys ]; then
  curl https://master.dl.sourceforge.net/project/afp/afp-Isabelle2019/afp-2019-08-19.tar.gz |
      tar -x -z -C ~/install/afp-2019 --strip 1
fi

if ! timeout --kill-after 1m $TIME_LIMIT "$ISABELLE_HOME/bin/isabelle" build -o threads=8 -b -v -d isabelle-thys -d ~/install/afp-2019/thys QRHL-Prerequisites; then
  echo "Build failed. Aborting without error to get a chance to upload the cache."
  exit 0
fi

git clone --depth 1 https://github.com/dominique-unruh/scala-isabelle.git ../scala-isabelle

echo "isabelle-home = $ISABELLE_HOME" > qrhl-tool.conf
echo "afp-root = $HOME/install/afp-2019" >> qrhl-tool.conf

# Kill the "while-sleep" loop
# pkill -P $$

echo $((TIME_LIMIT + $(cat ~/start-time) - $(date +%s))) > ~/remaining-time
cat ~/remaining-time

