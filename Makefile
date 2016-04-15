SRC = main.agda to-string.agda cedille-types.agda constants.agda cedille-main.agda spans.agda conversion.agda syntax-util.agda \
      rename.agda classify.agda subst.agda is-free.agda rec.agda lift.agda rewriting.agda ctxt.agda

cedille:	$(SRC) Makefile
		agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts -c main.agda 
		mv main cedille

cedille-prof:	$(SRC) Makefile
		agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts --ghc-flag=-prof --ghc-flag=-fprof-auto -c main.agda 
		mv main cedille-prof

cedille-main: cedille-main.agda
	agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts -c cedille-main.agda 

cedille-main.agda : cedille.gr ~/gratr2/src/gratr
	gratr --continue-with-nonterminating cedille.gr
