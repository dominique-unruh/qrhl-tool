VERSION="0.6alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy) doc/manual.pdf

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

.PHONY: doc/manual.pdf
doc/manual.pdf : 
	make -C doc manual.pdf

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt universal:packageBin

test-distrib0 : qrhl.zip
	rm -rf tmp
	unzip -d tmp qrhl.zip
	echo 'isabelle-home = /opt/Isabelle2019' > tmp/qrhl-$(VERSION)/qrhl-tool.conf
	echo 'afp-root = /opt/afp-2019' >> tmp/qrhl-$(VERSION)/qrhl-tool.conf

test-distrib : test-distrib0
	set -e && cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

test :
	sbt test

owncloud : qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl/

push_docker:
	docker login registry.gitlab.com
	docker build -t registry.gitlab.com/unruh/qrhl-tool/build-image src/docker
	docker push registry.gitlab.com/unruh/qrhl-tool/build-image

dropbox: qrhl.zip
	cp qrhl.zip ~/Dropbox/tmp
