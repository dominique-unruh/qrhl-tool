@echo off
set dir=%~dp0\..
pushd "%dir%" || exit /b 1
call sbt assembly || exit /b 1
popd
java "-Dfile.encoding=UTF-8" "-Dorg.slf4j.simpleLogger.defaultLogLevel=debug" "-Xss100M" "-jar" "%dir%\qrhl.jar" %* || exit /b 1
