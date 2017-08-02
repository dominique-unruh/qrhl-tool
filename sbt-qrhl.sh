#!/bin/bash

set -e

java -Dsbt.log.noformat=true -jar /home/unruh/.IdeaIC2017.2/config/plugins/Scala/launcher/sbt-launch.jar assembly
java -Dorg.slf4j.simpleLogger.defaultLogLevel=debug -jar qrhl.jar
