VERSION="0.4alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C ../queasycrypt/trunk upload

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	make -C ../queasycrypt/trunk manual.pdf
	sbt universal:packageBin

test-distrib : qrhl.zip
	unzip -d tmp qrhl.zip
	cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

owncloud : qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl/
