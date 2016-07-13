IAL=~/ial

SRCDIR=src

FILES = to-string.agda cedille.agda cedille-types.agda constants.agda cedille-main.agda \
	spans.agda conversion.agda syntax-util.agda \
	rename.agda classify.agda subst.agda is-free.agda rec.agda lift.agda rewriting.agda ctxt.agda \
        main.agda toplevel-state.agda process-cmd.agda general-util.agda options.agda options-types.agda options-main.agda

SRC = $(FILES:%=$(SRCDIR)//%)
OBJ = $(SRC:%.agda=%.agdai)

INC = -i $(SRCDIR) -i gratr-agda -i $(IAL)

cedille:	$(SRC) Makefile
		agda $(INC) --ghc-flag=-rtsopts -c $(SRCDIR)/main.agda 
		mv $(SRCDIR)/main cedille

cedille-prof:	$(SRC) Makefile
		agda $(INC) --ghc-flag=-rtsopts --ghc-flag=-prof --ghc-flag=-fprof-auto -c $(SRCDIR)/main.agda 
		mv $(SRCDIR)/main cedille-prof

cedille-main: $(SRCDIR)/cedille-main.agda
	agda $(INC) --ghc-flag=-rtsopts -c $(SRCDIR)/cedille-main.agda 

options-main: $(SRCDIR)/options-main.agda
	agda $(INC) -c $(SRCDIR)/options-main.agda 

clean:
	rm -f cedille $(SRCDIR)/main $(OBJ)
