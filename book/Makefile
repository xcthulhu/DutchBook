.PHONY: all clean

THEORIES := $(shell find .. -name \*.thy -print)

all: book.pdf

book.pdf: book.tex generated/snippets.tex $(THEORIES) bibliography.bib
	rm -f $@
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $<

book.bbl: book.tex book.aux
	bibtex book

generated/snippets.tex: $(THEORIES)
	isabelle build -c -v -d . Snippets
	touch $@

clean:
	latexmk -CA
	rm -rf generated
	rm -f *.log _region_.* *.aux *.fdb_latexmk texput.fls book.bbl comment.cut
	rm -rf auto/ _region_.prv/
