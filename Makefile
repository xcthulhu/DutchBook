.PHONY: all test test-DutchBook test-Extra

all: pdf

pdf:
	make -C book/

test: test-DutchBook test-Extra

test-DutchBook:
	isabelle build -o document=false -d . DutchBook

test-Extra:
	isabelle build -o document=false -d . Extra_Theories

THEORIES := $(shell find . -name \*.thy -print)
generated: $(THEORIES)
	isabelle build -d . Snippets 
	touch $@/

clean:
	$(CURDIR)/util/trash_heap.sh
	rm -rf generated/
