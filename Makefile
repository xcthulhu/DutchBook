.PHONY: all test test-DutchBook test-Extra

all: book/book.pdf dutchbook

book/book.pdf:
	make -C book/

dutchbook:
	isabelle build -c -v -d . DutchBook

test: test-Dutchbook test-Extra

test-Dutchbook:
	isabelle build -c -o document=false -d . Test_DutchBook

test-Extra:
	isabelle build -c -o document=false -d . Test_Extra_Theories

clean:
	$(CURDIR)/util/trash_heap.sh
	make -C book clean
	rm -rf output
