.PHONY: all test test-DutchBook test-Extra

all: book/book.pdf

book/book.pdf: generated/snippets.tex
	make -C book/

test: test-Dutchbook test-Extra

test-Dutchbook:
	isabelle build -c -o document=false -d . DutchBook

test-Extra:
	isabelle build -c -o document=false -d . Extra_Theories

clean:
	$(CURDIR)/util/trash_heap.sh
	make -C book clean
