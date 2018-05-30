# Cedille Core Checker v0.4


### To Do:
1. Imports
2. Lots of testing
3. Add a bunch of comments explaining what's going on (especially in CedilleCoreNorm)
4. "Let" terms/types?

### Index:
*  Check.hs       Functions that check a term/type/kind for errors and synthesize the type/kind/superkind of it
*  Ctxt.hs        Functions and types relating to the context
*  CedilleCore.hs Main I/O
*  Norm.hs        Functions that normalize/erase/substitute
*  Parser.hs      Parser
*  ToString.hs    As the name implies, turns terms/types/kinds into strings
*  Types.hs       Definitions of fundamental types for terms/types/kinds