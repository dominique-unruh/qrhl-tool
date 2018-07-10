VERSION="0.3alpha"
SOURCES := $(shell find src) $(wildcard examples/*.qrhl) $(wildcard examples/*.thy) $(wildcard isabelle-thys/*.thy) $(wildcard isabelle-thys/*.ML)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C .. upload

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin

# TODO remove
xxx : qrhl.zip
	mkdir -p tmp
	cd tmp && unzip -o ../qrhl.zip
