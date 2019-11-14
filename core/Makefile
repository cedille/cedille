
CEDILLE_CORE = Check.hs CedilleCore.hs Norm.hs Parser.hs Trie.hs Types.hs

all: cedille-core

cedille-core: $(CEDILLE_CORE) Makefile
	ghc -O -o ./CedilleCore -Werror -rtsopts -dynamic -i./ CedilleCore.hs --make
	mv CedilleCore cedille-core

cedille-core-mac: $(CEDILLE_CORE) Makefile
	ghc -O -o cedille-core-mac -Werror -rtsopts -optl-pthread -i./ CedilleCore.hs --make

cedille-core-static: $(CEDILLE_CORE) Makefile
	ghc -O -o cedille-core-static -Werror -rtsopts -optl-static -optl-pthread -i./ CedilleCore.hs --make

lines:
	wc -l $(CEDILLE_CORE)

clean:
	rm *.hi
	rm *.o
	rm cedille-core

profiling:
	ghc -prof -auto-all -O2 -Werror -rtsopts -o cedille-core CedilleCore.hs --make
