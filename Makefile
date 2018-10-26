VERSION="0.4alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy) doc/manual.pdf

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

.PHONY: doc/manual.pdf
doc/manual.pdf : 
	make -C doc manual.pdf

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin

test-distrib0 : qrhl.zip
	rm -rf tmp/qrhl-$(VERSION)/{bin,examples,manual.pdf,PG,proofgeneral.bat,proofgeneral.sh,README.md,run-isabelle.bat,run-isabelle.sh}
	unzip -d tmp qrhl.zip

test-distrib : test-distrib0
	cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

owncloud : qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl/
