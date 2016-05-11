FILES = main.agda to-string.agda cedille-types.agda constants.agda cedille-main.agda spans.agda conversion.agda syntax-util.agda \
      rename.agda classify.agda subst.agda is-free.agda rec.agda lift.agda rewriting.agda ctxt.agda

SRC = $(FILES:%=src/%)

INC = -i src -i ~/gratr2/agda -i ~/ial

cedille:	$(SRC) Makefile
		agda $(INC) --ghc-flag=-rtsopts -c src/main.agda 
		mv src/main cedille

cedille-prof:	$(SRC) Makefile
		agda $(INC) --ghc-flag=-rtsopts --ghc-flag=-prof --ghc-flag=-fprof-auto -c src/main.agda 
		mv src/main cedille-prof

cedille-main: cedille-main.agda
	agda $(INC) --ghc-flag=-rtsopts -c src/cedille-main.agda 

src/cedille-main.agda : src/cedille.gr ~/gratr2/src/gratr
	gratr --continue-with-nonterminating src/cedille.gr
