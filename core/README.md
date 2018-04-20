# Cedille Core

This is the first version, so it is very likely to contain several bugs.

## To Do:
1.  Parser (probably need to make several changes to the syntax from the specification, as several terms/types would cause parsing conflicts)
2.  Do lots of testing to find bugs, then fix them

## Index:
*  CedilleCoreCheck       Functions that check a term/type/kind for errors and synthesize the type/kind/superkind of it
*  CedilleCoreCtxt        Functions and types relating to the context
*  CedilleCoreNorm        Functions that normalize/erase/substitute
*  CedilleCoreToString    As the name implies, turns terms/types/kinds into strings
*  CedilleCoreTypes       Definitions of fundamental types for terms/types/kinds