VERSION="0.3alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy)

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

upload :
	make -C ../queasycrypt/trunk upload

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	make -C ../queasycrypt/trunk manual.pdf
	sbt universal:packageBin

# TODO remove
xxx : qrhl.zip
	mkdir -p tmp
	cd tmp && unzip -o ../qrhl.zip
	rm -fv tmp/qrhl-0.3alpha/lib/isabelle-temp/user/Isabelle2017/.isabelle/Isabelle2017/heaps/polyml-5.6_x86-linux/QRHL

test-distrib : qrhl.zip
	unzip -d tmp qrhl.zip
	cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

owncloud : qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl/
