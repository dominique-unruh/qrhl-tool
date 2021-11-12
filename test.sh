#!/bin/bash

#export QRHL_FORCE_BUILD=1
sbt 'testOnly -- -h target/test-reports'
xdg-open target/test-reports/index.html
