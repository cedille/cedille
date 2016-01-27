-- pull in Haskell Ints
module int where

open import bool
open import string

postulate 
  int : Set
  int0 : int
  int1 : int
  _+int_ : int → int → int
  _*int_ : int → int → int
  _-int_ : int → int → int
  string-to-int : string → int
  is-zero-int : int → 𝔹

{-# COMPILED_TYPE int Int #-}
{-# COMPILED int0 0 #-}
{-# COMPILED int1 1 #-}
{-# COMPILED _+int_ (+) #-}
{-# COMPILED _*int_ (*) #-}
{-# COMPILED _-int_ (-) #-}
{-# COMPILED string-to-int (\ x -> read x :: Int) #-}
{-# COMPILED is-zero-int ((==) 0) #-}