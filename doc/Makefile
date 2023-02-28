
std : manual.pdf

.DELETE_ON_ERROR:

declmath.sty :
	if ! [ -d declmath ]; then \
		git clone --depth=1 'https://github.com/dominique-unruh/declmath.git'; fi
	for f in declmath.sty makesymind.py; do \
		ln -sf declmath/"$$f" .; done
%.qrhl.lst : ../examples/%.qrhl format-for-listings.py
	python3 format-for-listings.py $< >$@
%.thy.lst : ../examples/%.thy format-for-listings.py
	python3 format-for-listings.py $< >$@

manual.pdf : manual.tex qrhl.bib declmath.sty macros.tex example.qrhl.lst Example.thy.lst PrgEnc.thy.lst prg-enc-rorcpa.qrhl.lst prg-enc-indcpa.qrhl.lst PrgEnc.thy.lst equality.qrhl.lst Teleport.thy.lst Code_Example.thy.lst qrhl.aux preamble.tex
	rm -f manual.aux manual.bbl manual-blx.bib manual.out
	-pdflatex --synctex=1 -interaction batchmode manual
	bibtex manual
	python2 makesymind.py manual
	makeindex manual
	pdflatex --synctex=1 -interaction batchmode manual
	bibtex manual
	python2 makesymind.py manual
	makeindex manual
	pdflatex --synctex=1 -interaction batchmode manual
	bibtex manual
	python2 makesymind.py manual
	makeindex manual
	pdflatex --synctex=1 -interaction batchmode manual
	if grep 'LaTeX Warning: There were undefined references' manual.log; then false; fi
	if pdftotext manual.pdf - | grep 'THIS IS A DRAFT'; then false; fi

qrhl.aux :
	git archive --remote=git@gitlab.com:unruh/qrhl-paper.git arxiv-v2 qrhl.aux | tar -xvm
