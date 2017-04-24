.PHONY: test

test:
	isabelle build -o document=false -d . DutchBook
	isabelle build -o document=false -d . Extra_Theories
