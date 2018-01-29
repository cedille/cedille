IAL=~/ial

AGDA=agda
#AGDA=/home/astump/agda-2.5.1.2/.cabal-sandbox/bin/agda

SRCDIR=src

AUTOGEN = cedille.agda cedille-types.agda cedille-main.agda \
          options.agda options-types.agda options-main.agda \
          cws.agda cws-types.agda cws-main.agda

GRAMMARS = cedille.gr options.gr cws.gr

AGDASRC = to-string.agda constants.agda \
	spans.agda conversion.agda syntax-util.agda ctxt-types.agda \
	rename.agda classify.agda subst.agda is-free.agda lift.agda rewriting.agda ctxt.agda \
        main.agda toplevel-state.agda process-cmd.agda general-util.agda interactive-cmds.agda erased-spans.agda \
	rkt.agda type-inf.agda

CEDILLE_ELISP = cedille-mode.el cedille-mode/cedille-mode-context.el cedille-mode/cedille-mode-errors.el \
                cedille-mode/cedille-mode-faces.el cedille-mode/cedille-mode-highlight.el \
                cedille-mode/cedille-mode-info.el cedille-mode/cedille-mode-library.el cedille-mode/cedille-mode-summary.el cedille-mode/cedille-mode-normalize.el cedille-mode/cedille-mode-scratch.el cedille-mode/cedille-mode-beta-reduce.el

SE_MODE = se-mode/se.el se-mode/se-helpers.el se-mode/se-highlight.el se-mode/se-inf.el se-mode/se-macros.el se-mode/se-mode.el se-mode/se-navi.el se-mode/se-pin.el

ELISP=$(SE_MODE) $(CEDILLE_ELISP)

FILES = $(AUTOGEN) $(AGDASRC)

SRC = $(FILES:%=$(SRCDIR)//%)
OBJ = $(SRC:%.agda=%.agdai)

LIB = --library-file=libraries --library=ial --library=gratr-agda --library=cedille

all: cedille # elisp

libraries: 
	./create-libraries.sh

cedille:	$(SRC) Makefile libraries
		$(AGDA) $(LIB) --ghc-flag=-rtsopts -c $(SRCDIR)/main.agda 
		mv $(SRCDIR)/main cedille

elisp: $(SE_MODE:%.el=%.elc) $(ELISP:%.el=%.elc)

%.elc: %.el
	emacs --batch -L se-mode -L cedille-mode -f batch-byte-compile $<

cedille-prof:	$(SRC) Makefile
		$(AGDA) $(LIB) --ghc-flag=-rtsopts --ghc-flag=-prof --ghc-flag=-fprof-auto -c $(SRCDIR)/main.agda 
		mv $(SRCDIR)/main cedille-prof

cedille-main: $(SRCDIR)/cedille-main.agda
	$(AGDA) $(LIB) --ghc-flag=-rtsopts -c $(SRCDIR)/cedille-main.agda 

options-main: $(SRCDIR)/options-main.agda
	$(AGDA) $(LIB) -c $(SRCDIR)/options-main.agda 

cws-main: $(SRCDIR)/cws-main.agda
	$(AGDA) $(LIB) -c $(SRCDIR)/cws-main.agda 

clean:
	rm -f cedille $(SRCDIR)/main $(OBJ)

lines:
	wc -l $(AGDASRC:%=$(SRCDIR)//%) $(GRAMMARS:%=$(SRCDIR)//%) $(CEDILLE_ELISP)

elisp-lines:
	wc -l $(CEDILLE_ELISP)

grammar-lines:
	wc -l $(GRAMMARS:%=$(SRCDIR)//%)

agda-lines:
	wc -l $(AGDASRC:%=$(SRCDIR)//%)

