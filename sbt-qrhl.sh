#!/bin/bash

set -e

sbt assembly
java -Dorg.slf4j.simpleLogger.defaultLogLevel=debug -jar qrhl.jar "$@"
