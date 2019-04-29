# Cedille 1.1.1

- support for simple inference of motives for pattern matches.  This probably
  should have been 1.1, but we are releasing it now.  It is demo'ed in the
  language-overview/datatypes.ced file.
- Cedille Core checker now uses de Bruijn indices for bound variables, and
  runs quite a bit faster now.
- you no longer need to parenthesize mu and mu' expressions if you are 
  applying them to arguments.

# Cedille 1.1

- support for datatype notations.  See language-overview/datatypes.ced and 
  language-overview/cov-pattern-matching.ced.  Please note that "data"
  and "close" are now keywords and cannot be used as identifiers in Cedille
  code.
- elaboration to Cedille Core with keystroke "E", and checking of generated
  .cdle files from within emacs using the Cedille Core checker.
- colon is now allowed instead of left triangle for classifications.
- better support for implicit arguments with let-terms; see
  language-overview/local-definitions.ced.
- reversed the direction of rewriting for synthesizing rhos, for the
  benefit of checking in Cedille Core
- various bug fixes 

# Cedille 1.0

- initial release
