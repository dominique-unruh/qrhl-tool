#!/bin/bash

set -e

java -Dsbt.log.noformat=true -jar /home/unruh/.IdeaIC2017.1/config/plugins/Scala/launcher/sbt-launch.jar assembly
java -jar qrhl.jar
