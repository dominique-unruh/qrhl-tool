VERSION="0.7.1"
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
	echo 'isabelle-home = /opt/Isabelle2020' > tmp/qrhl-$(VERSION)/qrhl-tool.conf
	echo 'afp-root = /opt/afp-2020' >> tmp/qrhl-$(VERSION)/qrhl-tool.conf

test-distrib : test-distrib0
	set -e && cd tmp/qrhl-$(VERSION)/examples && \
		for i in *.qrhl; do ../bin/qrhl "$$i"; done

test-pqfo : test-distrib
	QRHL_DIR="$$PWD/tmp/qrhl-$(VERSION)" && cd ../pq-fo-verify/proofs && git pull && "$$QRHL_DIR/bin/qrhl" all.qrhl

test-hsku : test-distrib
	QRHL_DIR="$$PWD/tmp/qrhl-$(VERSION)" && cd ../hksu-verification && git pull && "$$QRHL_DIR/bin/qrhl" all.qrhl

test :
	sbt test

owncloud : qrhl.zip
	cp -v qrhl.zip /home/unruh/ownCloud/qrhl/

docker: qrhl.zip
	docker build . -f src/docker/Dockerfile -t ghcr.io/dominique-unruh/qrhl-tool:latest
	docker push ghcr.io/dominique-unruh/qrhl-tool:latest

docker-login:
	docker login ghcr.io -u dominique-unruh

dropbox: qrhl.zip
	cp qrhl.zip ~/Dropbox/tmp

view-test-results:
	rm -rf target/tmp
	mkdir target/tmp
	cd target/tmp && gh run download
	if [ -e target/tmp/index.html ]; then xdg-open target/tmp/index.html; else xdg-open target/tmp; fi

issue :
	gh issue create --assignee @me --milestone 0.8
