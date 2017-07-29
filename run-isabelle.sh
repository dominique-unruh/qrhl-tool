#!/bin/bash

set -e

java -jar /home/unruh/.IdeaIC2017.2/config/plugins/Scala/launcher/sbt-launch.jar "run --isabelle /opt/Isabelle2016-1 $*"
