module parser where
open import lib
open import cedille-types

{-# FOREIGN GHC import qualified CedilleParser #-}

data Either (A : Set)(B : Set) : Set where
  Left : A → Either A B
  Right : B → Either A B
{-# COMPILE GHC Either = data Either (Left | Right) #-}

postulate
  parseStart  : string → Either (Either string string) start
  parseTerm : string → Either string term
  parseType : string → Either string type
  parseKind : string → Either string kind
  parseLiftingType : string → Either string liftingType
  parseDefTermOrType : string → Either string defTermOrType

{-# COMPILE GHC parseStart = CedilleParser.parseTxt #-}
{-# COMPILE GHC parseTerm = CedilleParser.parseTerm #-}
{-# COMPILE GHC parseType = CedilleParser.parseType #-}
{-# COMPILE GHC parseKind = CedilleParser.parseKind #-}
{-# COMPILE GHC parseLiftingType = CedilleParser.parseLiftingType #-}
{-# COMPILE GHC parseDefTermOrType = CedilleParser.parseDefTermOrType #-}
