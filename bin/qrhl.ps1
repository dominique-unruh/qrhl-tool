$dir = Split-Path -Parent $PSScriptRoot
java "-Dfile.encoding=UTF-8" "-Dorg.slf4j.simpleLogger.defaultLogLevel=debug" "-Xss100M" "-jar" "$dir/qrhl.jar" $args
