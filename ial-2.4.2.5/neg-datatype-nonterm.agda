{-# OPTIONS --no-positivity-check #-}

{- This file gives a standard example showing that if arguments to
   constructors can use the datatype in a negative position (to the
   left of one or an odd number of arrows), then termination and 
   logical consistency is lost. -}

module neg-datatype-nonterm where

open import empty

data Bad : Set where
  bad : (Bad → ⊥) → Bad

badFunc : Bad → ⊥
badFunc (bad f) = f (bad f)

-- if you try to normalize the following, it will diverge
inconsistency : ⊥
inconsistency = badFunc (bad badFunc)