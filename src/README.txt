cedille.agda		parser, generated from cedille.gr
cedille.gr		main grammar for Cedille input files
cedille-main.agda       a test tool which can parse Cedille files, generated from cedille.gr
cedille-types.agda	abstract syntax trees for Cedille, generated from cedille.gr
classify.agda		type-checking code
classify-tests.agda     tests for classify.agda
constants.agda          a few constants defined for Cedille
conversion.agda		implements conversion functions and head-normal form
ctxt.agda		implements the type-checking context
cws.gr                  grammar for comments and whitespace for Cedille input files
cws.agda                parser, generated from cws.gr
cws-types.agda          syntax trees, generated from cws.gr
cws-main.agda           a test tool which can parse Cedille files, generated from cws.gr
general-util.agda       things I want to add to the IAL but have been holding off on for versioning reasons
hnf-tests.agda          tests (probably currently broken) for hnf
interactive-cmds.agda   interactive command handlers (ineractively normalizing, erasing, and beta-reducing)
is-free.agda            checking if a variable is free in an expression
lift.agda               code related to lifting
lift-tests.agda         test code for lifting
main.agda               the main file which is compiled to the cedille backend
Makefile                dummy Makefile which just calls the one you will find one directory up
options.gr              grammar for the ~/.cedille/options file
options.agda            parser, generated from options.gr
options-main.agda       a test tool which can parse Cedille files, generated from options.gr
options-types.agda      syntax trees, generated from options.gr
process-cmd.agda        code for processing top-level commands
rec.agda                code for processing rec-commands specifically
rename.agda             some code related to variable renaming
rewriting.agda          code for rewriting a term to another term in an expression
spans.agda              code related to spans, which the backend produces for the benefit of the frontend
subst.agda              code for substituting into an expression
syntax-util.agda        some basic utilities for manipulating Cedille syntax trees
toplevel-state.agda     data structures for the top-level state of the backend tool
to-string.agda          code for converting expressions to strings
to-string-tests.agda    tests for to-string
