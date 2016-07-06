IAL=~/ial

FILES = to-string.agda cedille.agda cedille-types.agda constants.agda cedille-main.agda \
	spans.agda conversion.agda syntax-util.agda \
	rename.agda classify.agda subst.agda is-free.agda rec.agda lift.agda rewriting.agda ctxt.agda \
        main.agda toplevel-state.agda process-cmd.agda general-util.agda options.agda options-types.agda options-main.agda

SRC = $(FILES:%=src/%)
OBJ = $(SRC:%.agda=%.agdai)

INC = -i src -i gratr-agda -i $(IAL)

cedille:	$(SRC) Makefile
		agda $(INC) --ghc-flag=-rtsopts -c src/main.agda 
		mv src/main cedille

cedille-prof:	$(SRC) Makefile
		agda $(INC) --ghc-flag=-rtsopts --ghc-flag=-prof --ghc-flag=-fprof-auto -c src/main.agda 
		mv src/main cedille-prof

cedille-main: src/cedille-main.agda
	agda $(INC) --ghc-flag=-rtsopts -c src/cedille-main.agda 

options-main: src/options-main.agda
	agda $(INC) -c src/options-main.agda 

# this requires gratr
#src/cedille-main.agda : src/cedille.gr 
#	cd src ; gratr --continue-with-nonterminating cedille.gr

# this requires gratr
#src/options-main.agda : src/options.gr 
#	cd src ; gratr options.gr

clean:
	rm -f cedille src/main $(OBJ)
