
CEDILLE_CORE = Check.hs Ctxt.hs CedilleCore.hs Norm.hs Parser.hs ToString.hs Types.hs

all: cedille-core

cedille-core: $(CEDILLE_CORE) Makefile
	ghc -O -o cedille-core -Werror -rtsopts -i./ CedilleCore.hs --make

cedille-core-static: $(CEDILLE_CORE) Makefile
	ghc -O -o cedille-core -Werror -rtsopts -optl-static -optl-pthread -i./ CedilleCore.hs --make

cedille-core-lines:
	wc -l $(CEDILLE_CORE)

clean:
	rm *.hi
	rm *.o
	rm cedille-core

profiling:
	ghc -prof -auto-all -o cedille-core CedilleCore.hs
