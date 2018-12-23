.PHONY: all test test-DutchBook test-Extra

all: book/book.pdf

book/book.pdf: generated/snippets.tex
	make -C book/

test: test-Dutchbook test-Extra

test-Dutchbook:
	isabelle build -o document=false -d . DutchBook

test-Extra:
	isabelle build -o document=false -d . Extra_Theories

THEORIES := $(shell find . -name \*.thy -print)
generated/snippets.tex: $(THEORIES)
	isabelle build -c -v -d . Snippets
	touch $@

clean:
	$(CURDIR)/util/trash_heap.sh
	make -C book clean
	rm -rf generated/
