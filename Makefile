VERSION="0.3alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C .. upload

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin

local-isabelle :
	/opt/Isabelle2018-RC0/bin/isabelle jedit -s -l Lots-Of-Stuff ~/svn/queasycrypt/trunk/qrhl-tool/src/main/isabelle/Test.thy &

tmp : qrhl.zip
	unzip -d tmp qrhl.zip
	cd tmp && echo isabelle. | bin/qrhl
