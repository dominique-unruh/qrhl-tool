VERSION="0.1alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C .. upload-tool

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt packageBin
