COQC=coqc
COQDEP=coqdep
COQDOC=coqdoc

HTMLDOC=$$HOME/public_html/coindsem/doc

FILES=semantics.v compilation.v typing.v densem.v cps.v traces.v

all: $(FILES:.v=.vo)

documentation:
	$(COQDOC) --html -d $(HTMLDOC) $(FILES:%.v=--glob-from %.glob) $(FILES)
	tar czf $(HTMLDOC)/src.tgz Makefile .depend $(FILES)
clean:
	rm -f *.vo *.glob

.SUFFIXES: .v .vo

.v.vo:
	$(COQC) -dump-glob $*.glob $*.v

depend:
	$(COQDEP) $(FILES) > .depend

include .depend
