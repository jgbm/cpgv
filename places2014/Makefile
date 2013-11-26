all: cpgv.pdf

cpgv.aux: cpgv.tex
	pdflatex cpgv

cpgv.bbl: cpgv.aux cpgv.bib
	bibtex cpgv

cpgv.pdf: cpgv.aux cpgv.bbl
	pdflatex cpgv
	pdflatex cpgv

clean:
	rm -f cpgv.pdf cpgv.aux cpgv.out cpgv.log cpgv.blg cpgv.bbl
