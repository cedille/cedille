
CEDILLE_CORE = Check.hs Ctxt.hs CedilleCore.hs Norm.hs Parser.hs ToString.hs Types.hs

all: cedille-core

cedille-core: $(CEDILLE_CORE) Makefile
	ghc -O -o ./CedilleCore -Werror -rtsopts -dynamic -i./ CedilleCore.hs --make
	mv CedilleCore cedille-core

cedille-core-static: $(CEDILLE_CORE) Makefile
	ghc -O -o ./CedilleCore -Werror -rtsopts -dynamic -optl-static -optl-pthread -i./ CedilleCore.hs --make
	mv CedilleCore cedille-core-static

cedille-core-lines:
	wc -l $(CEDILLE_CORE)
