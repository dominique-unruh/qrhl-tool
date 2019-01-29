VERSION="0.5alpha"
SOURCES := $(shell find src) $(wildcard *.qrhl) $(wildcard *.thy) doc/manual.pdf

qrhl.zip : target/universal/qrhl-$(VERSION).zip
	cp $< $@

.PHONY: doc/manual.pdf
doc/manual.pdf : 
	make -C doc manual.pdf

target/universal/qrhl-$(VERSION).zip : build.sbt $(SOURCES)
	sbt managedResources # Makes sure that the next sbt command sees all files in isabelle-afp
	-patch <patch isabelle-afp/Polynomial_Interpolation/Missing_Polynomial.thy
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
	set -e && cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

test :
	sbt test

owncloud : test qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl/

push_docker:
	docker login registry.gitlab.com
	docker build -t registry.gitlab.com/unruh/qrhl-tool/build-image docker-dir
	docker push registry.gitlab.com/unruh/qrhl-tool/build-image
