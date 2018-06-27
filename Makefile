VERSION="0.2"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C .. upload

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin

local-isabelle :
	/opt/Isabelle2018-RC0/bin/isabelle jedit -s -l Lots-Of-Stuff ~/svn/queasycrypt/trunk/qrhl-tool/src/main/isabelle/Test.thy &
