all: main.pdf

main.aux: main.tex
	pdflatex main

main.bbl: main.aux main.bib
	bibtex main

main.pdf: main.aux main.bbl
	pdflatex main
	pdflatex main

clean:
	rm -f main.pdf main.aux main.out main.log main.blg main.bbl
