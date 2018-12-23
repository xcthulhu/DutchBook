THEORIES := $(shell find .. -name \*.thy -print)
book.pdf: book.tex generated/snippets.tex $(THEORIES) bibliography.bib
	rm -f $@
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $<

book.bbl: book.tex book.aux 
	bibtex book

generated/snippets.tex: generated $(THEORIES)

generated: ../generated
	rm -f $@
	[ -d $< ]
	ln -s $< $@

../generated: $(THEORIES)
	make -C .. generated

clean:
	latexmk -CA
	rm -f *.log _region_.* *.aux *.fdb_latexmk texput.fls generated book.bbl comment.cut
	rm -rf auto/ _region_.prv/
