module test where

open import cedille-types

{-# IMPORT CedilleParser #-}

data Either (A : Set)(B : Set) : Set where
  Left : A → Either A B
  Right : B → Either A B
{-# COMPILED_DATA Either Either Left Right #-}

postulate
  parseStart  : string → Either string start
  showStart   : start  -> string

{-# COMPILED parseStart CedilleParser.parseTxt #-}
{-# COMPILED showStart  CedilleParser.showStart #-}

data ⊤ : Set where
  triv : ⊤

{-# COMPILED_DATA ⊤ () ()  #-}

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 1 _>>=_
infixl 1 _>>_

----------------------------------------------------------------------
-- postulated operations
----------------------------------------------------------------------

postulate
  return : ∀ {A : Set} → A → IO A
  _>>=_  : ∀ {A B : Set} → IO A → (A → IO B) → IO B

{-# COMPILED return (\ _ -> return )   #-}
{-# COMPILED _>>=_  (\ _ _ -> (>>=)) #-}

_>>_ : ∀ {A B : Set} → IO A → IO B → IO B
x >> y = x >>= (λ q -> y)

postulate
  putStr : string -> IO ⊤

{-# IMPORT Data.Text.IO #-}
{-# COMPILED putStr         Data.Text.IO.putStr                #-}

test_str : string
test_str = "module Cnat. cNat ◂ ★ = ∀ X : ★ . (X ➔ X) ➔ X ➔ X . cZ ◂ cNat = Λ X . λ f . λ a . a . cS ◂ cNat ➔ cNat = λ n . Λ X . λ f . λ a . f (n · X f a) . "

test2 : Either string start
test2 = parseStart test_str

main : IO ⊤
main with test2 
... | Left s  = putStr s
... | Right r = putStr (showStart r) >> putStr "\n"

