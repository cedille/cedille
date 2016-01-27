-- mostly adapted from Agda stdlib

module level where

import Agda.Primitive 

open Agda.Primitive public
  using    (Level ; _⊔_ ; lsuc ; lzero)

level = Level

lone : level
lone = lsuc lzero

record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
