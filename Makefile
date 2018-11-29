ARCH=amd64
VERSION=0.4alpha
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy) doc/manual.pdf

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

.DELETE_ON_ERROR :

#.PHONY: doc/manual.pdf
doc/manual.pdf : $(wildcard doc/*.tex)
	make -C doc manual.pdf

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin

test-distrib0 : qrhl.zip
	-rm -f tmp/qrhl-$(VERSION)/*
	rm -rf tmp/qrhl-$(VERSION)/lib
	rm -rf tmp/qrhl-$(VERSION)/examples
	rm -rf tmp/qrhl-$(VERSION)/bin
	rm -rf tmp/qrhl-$(VERSION)/PG
	rm -rf tmp/qrhl-$(VERSION)/isabelle-afp
	rm -rf tmp/qrhl-$(VERSION)/isabelle-thys
	unzip -d tmp qrhl.zip

test-distrib : test-distrib0
	cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

owncloud : qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl/


target/snapcraft/$(VERSION) : qrhl.zip
	#rm -rf $@/ # TODO restore
	mkdir -p target/snapcraft
	unzip -d $@/ qrhl.zip
	cd $@/qrhl-$(VERSION) && ( echo isabelle. | bin/qrhl )

qrhl-tool_$(VERSION)_$(ARCH).snap : target/snapcraft/$(VERSION)
	snapcraft clean qrhl-tool -s pull
	sudo snapcraft cleanbuild

install_snap : qrhl-tool_$(VERSION)_$(ARCH).snap
	sudo snap install --devmode $<

test_snap : install_snap
	snap run qrhl-tool.test
