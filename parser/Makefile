.PHONY: cedille-parser cedille-lexer cedille-comments-lexer cedille-options-parser cedille-options-lexer

cedille-parser: cedille-lexer
	cd src/;happy CedilleParser.y; mv CedilleParser.hs ../../src;cd ..;

cedille-lexer:
	cd src/; alex CedilleLexer.x; mv CedilleLexer.hs ../../src;cd ..;

cedille-options-parser: cedille-options-lexer
	cd src/;happy CedilleOptionsParser.y; mv CedilleOptionsParser.hs ../../src;cd ..;

cedille-options-lexer:
	cd src/; alex CedilleOptionsLexer.x; mv CedilleOptionsLexer.hs ../../src;cd ..;

cedille-comments-lexer:
	cd src/; alex CedilleCommentsLexer.x; mv CedilleCommentsLexer.hs ../../src; cd ..;

parser: ./src/CedilleParser.y ./src/CedilleLexer.x ./src/CedilleCommentsLexer.x Makefile
	cd src/; alex CedilleCommentsLexer.x; alex CedilleLexer.x; happy CedilleParser.y; mv CedilleCommentsLexer.hs ../../src; mv CedilleLexer.hs ../../src; mv CedilleParser.hs ../../src;

console:
	cabal repl

test-console:
	cabal repl tests

backup: clean
	tar czvf ../cedilleparser-$(shell date --iso=seconds).tar.gz .

tests:
	cabal test

tests-debug: compile-tests-debug
	./test/Tests

compile-tests-debug: parser-debug lexer ast
	cd test; ghc -i../src Tests.hs; 

ast:    lexer
	cd src; ghc CedilleTypes.hs

parser-debug : lexer
	cd src;	happy -i -d -a CedilleParser.y

parser-executable: ./src/CedilleParser.y lexer
	cp ../src/CedilleTypes.hs src/;	cd src;	happy CedilleParser.y; ghc --make CedilleParser.hs -main-is CedilleParser; mv CedilleParser ..; rm CedilleTypes.hs

parser-options-lexer-executable: lexer-options
	cd src;	ghc --make CedilleOptionsLexer.hs -main-is CedilleOptionsLexer; mv CedilleOptionsLexer ..; 

parser-options-executable: ./src/CedilleOptionsParser.y lexer-options
	cd src;	happy CedilleOptionsParser.y; ghc --make CedilleOptionsParser.hs -main-is CedilleOptionsParser; mv CedilleOptionsParser ..; 

lexer:  ./src/CedilleLexer.x
	cd src; alex CedilleLexer.x 

lexer-options:  ./src/CedilleOptionsLexer.x
	cd src; alex CedilleOptionsLexer.x 

lexer-comments:  ./src/CedilleCommentsLexer.x
	cd src; alex CedilleCommentsLexer.x 

lexer-comments-executable:  ./src/CedilleCommentsLexer.x
	cd src; alex CedilleCommentsLexer.x; ghc --make CedilleCommentsLexer.hs -main-is CedilleCommentsLexer; mv CedilleCommentsLexer ..;

info:   
	happy -i src/CedilleParser.y; rm -f src/CedilleParser.hs; rm -f src/CedilleLexer.hs ; rm -f src/*.hi; rm -f src/*.o

clean:
	rm -f CedilleParser;rm -f src/*.info; rm -f src/CedilleParser.hs; rm -f src/CedilleParser.info; rm -f src/CedilleLexer.hs ; rm -f src/*.hi; rm -f src/*.o; rm -f src/*.agdai; rm -rf src/MAlonzo; rm -f agda-test; rm -f *~; rm -f src/*~; rm -f test/*~; rm -rf dist; rm -f test/*.o; rm -f test/*.hi; rm -f test/#*; rm -f test/.#*; rm -f results/*; rm -f agda-test-comments; rm -f src/CedilleCommentsLexer.hs

agda-test: ./src/cedille-types.agda ./src/test.agda parser lexer
	cd src;agda --ghc-flag=-rtsopts -c test.agda;mv test ../agda-test;cd ..;./agda-test

agda-test-comments: ./src/cws-types.agda ./src/testComments.agda lexer-comments
	cd src;agda --ghc-flag=-rtsopts -c testComments.agda;mv testComments ../agda-test-comments;cd ..;./agda-test-comments

conflict-image: ./doc/conflicts/derivation.dot
	cd doc/conflicts/;dot derivation.dot -Tjpg -o derivation.jpg 
