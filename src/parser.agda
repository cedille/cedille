module parser where
open import lib
open import cedille-types

{-# IMPORT CedilleParser #-}

data Either (A : Set)(B : Set) : Set where
  Left : A → Either A B
  Right : B → Either A B
{-# COMPILED_DATA Either Either Left Right #-}

postulate
  parseStart  : string → Either (Either string string) start
  parseTerm : string → Either string term
  parseType : string → Either string type
  parseKind : string → Either string kind
  parseLiftingType : string → Either string liftingType
  parseDefTermOrType : string → Either string defTermOrType

{-# COMPILED parseStart CedilleParser.parseTxt #-}
{-# COMPILED parseTerm CedilleParser.parseTerm #-}
{-# COMPILED parseType CedilleParser.parseType #-}
{-# COMPILED parseKind CedilleParser.parseKind #-}
{-# COMPILED parseLiftingType CedilleParser.parseLiftingType #-}
{-# COMPILED parseDefTermOrType CedilleParser.parseDefTermOrType #-}
