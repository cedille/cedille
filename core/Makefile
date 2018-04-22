
CedilleCoreHaskell = CedilleCoreCheck.hs CedilleCoreCtxt.hs CedilleCoreMain.hs CedilleCoreNorm.hs CedilleCoreToString.hs CedilleCoreTypes.hs

CedilleCoreParser = CedilleCoreParser.y CedilleCoreLexer.x
CedilleCoreParserCompiled = CedilleCoreParser.y CedilleCoreLexer.x CedilleCoreParser.hs CedilleCoreLexer.hs

CedilleCore = $(CedilleCoreHaskell) $(CedilleCoreParser)

all:
	make cedille-core-parser;
	make cedille-core-lexer;
	make cedille-core-haskell

cedille-core-parser:
	happy CedilleCoreParser.y

cedille-core-lexer:
	alex CedilleCoreLexer.x

cedille-core-haskell:
	ghc CedilleCoreMain.hs

haskell-lines:
	wc -l $(CedilleCoreHaskell)

parser-lines:
	wc -l $(CedilleCoreParser)

parser-compiled-lines:
	wc -l $(CedilleCoreParserCompiled)

cedille-core-lines:
	wc -l $(CedilleCore)
