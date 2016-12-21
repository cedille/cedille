Various attempt at higher-order lambda encoding of untyped lambda calculus terms,
mostly inspired by parametricity (approach 1, the only approach that is actually
working so far to define constructors and be able to prove some theorems, namely
depth-size).

Approach 1:

-- ctrm.ced: a type (ctrm) for Church-encoded open pure lambda terms.

-- trm.ced: a type (trm) for intrinsically parametric open pure lambda terms.

-- ctors.ced: constructors for trm.  

Approach 2:

   Like approach 1 except try to include cut-elimination as part of the definition

   trm0, ctors0

Approach 3:

   Intrinsically inductive (not parametric) terms

-- ctrm0.ced
-- ind-trm.ced

