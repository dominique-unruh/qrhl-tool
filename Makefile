VERSION="0.3"
SOURCES := $(shell find src) $(wildcard examples/*.qrhl) $(wildcard examples/*.thy) $(wildcard isabelle-thys/*.thy) $(wildcard isabelle-thys/*.ML)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C .. upload

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin

test-distrib0 : qrhl.zip
	unzip -d tmp qrhl.zip

test-distrib : test-distrib0
	cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

owncloud : qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl-aec.zip
