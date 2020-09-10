VERSION="0.6alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy) doc/manual.pdf

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

.PHONY: doc/manual.pdf
doc/manual.pdf : 
	make -C doc manual.pdf

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt managedResources # Makes sure that the next sbt command sees all files in isabelle-afp
	sbt universal:packageBin

test-distrib0 : qrhl.zip
	-rm -f tmp/qrhl-$(VERSION)/*
	rm -rf tmp/qrhl-$(VERSION)/lib
	rm -rf tmp/qrhl-$(VERSION)/examples
	rm -rf tmp/qrhl-$(VERSION)/bin
	rm -rf tmp/qrhl-$(VERSION)/PG
	rm -rf tmp/qrhl-$(VERSION)/isabelle-afp
	rm -rf tmp/qrhl-$(VERSION)/isabelle-thys
	rm -rf tmp/qrhl-$(VERSION)/conf
	unzip -d tmp qrhl.zip

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
