#main: main.agda
#	agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts -c main.agda 

cedille-main: cedille-main.agda
	agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts -c cedille-main.agda 

cedille-main.agda : cedille.gr ~/gratr2/src/gratr
	gratr --continue-with-nonterminating cedille.gr
