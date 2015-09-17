GRATR=~/gratr
IAL=~/ial

main: main.agda check.agda syntax-util.agda rename.agda cedille-main.agda defeq.agda subst.agda conversion.agda lift.agda free.agda normalize.agda synth.agda
	agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts -c main.agda 

cedille-main: cedille-main.agda
	agda -i . -i ~/gratr2/agda -i ~/ial --ghc-flag=-rtsopts -c cedille-main.agda 

cedille-main.agda : cedille.gr ~/gratr2/src/gratr
	gratr --continue-with-nonterminating --debug-compilation-to-agda --skip-unambiguity-check cedille.gr