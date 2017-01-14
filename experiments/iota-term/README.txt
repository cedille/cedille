Higher-order lambda encoding of untyped lambda calculus terms, based on parametricity.

-- ctrm.ced:      Church-encoded (non-dependent) untyped lambda calculus terms, and related functions
-- trm.ced:       parametric such terms (ptrm); a version which is extensional in the variable interpretation (ptrme); and the
                  final type (trm), for which we prove induction in ind.ced.
-- ctors.ced:     definitions of constructors var and app for the trm type
-- ctors-lam.ced: definition of the constructor lam (quite involved)
-- ind.ced:       derivation of induction for trm
-- Trm.ced:       import this to get the interesting definitions from this directory

Also: explanation.ced has some rough notes I took while figuring out how to type the lam constructor.
