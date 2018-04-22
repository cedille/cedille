# Cedille Core Checker v0.2


### Changelog:
*  Added I/O functions (main)
*  Changed pi-kinds to use lower case pi, to avoid confusing them with types in foralls/type lambdas (the parser defaulted to assuming they were types and threw an error if it encountered a star)
*  Fixed some bugs relating to hnf/substitution/conversion (and switched eta-contractions to occur in hnf instead of in conversion)
*  Added "_" for binder variables
*  Removed unused functions (is-free) and shortened up code (merged hnf and subst)
*  Added Makefile

### To Do:
1. Lots of testing
2. Add a bunch of comments explaining what's going on (especially in CedilleCoreNorm)
2. "Let" terms/types?

### Index:
*  CedilleCoreCheck.hs       Functions that check a term/type/kind for errors and synthesize the type/kind/superkind of it
*  CedilleCoreCtxt.hs        Functions and types relating to the context
*  CedilleCoreLexer.x        Lexer
*  CedilleCoreMain.hs        I/O
*  CedilleCoreNorm.hs        Functions that normalize/erase/substitute
*  CedilleCoreParser.y       Parser
*  CedilleCoreToString.hs    As the name implies, turns terms/types/kinds into strings
*  CedilleCoreTypes.hs       Definitions of fundamental types for terms/types/kinds