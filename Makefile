VERSION="0.2"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C .. upload

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin
