.PHONY: all test test-DutchBook test-Extra

all: dutchbook book/book.pdf

book/book.pdf:
	make -C book/

dutchbook:
	isabelle build -c -v -d . DutchBook

test: test-Dutchbook test-Extra

clean:
	$(CURDIR)/util/trash_heap.sh
	make -C book clean
	rm -rf output
