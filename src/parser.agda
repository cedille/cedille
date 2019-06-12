module parser where
open import lib
open import cedille-types

{-# FOREIGN GHC import qualified CedilleParser #-}

data Either (A : Set)(B : Set) : Set where
  Left : A → Either A B
  Right : B → Either A B
{-# COMPILE GHC Either = data Prelude.Either (Prelude.Left | Prelude.Right) #-}

postulate
  parseStart  : string → Either (Either string string) ex-file
  parseTerm : string → Either string ex-tm
  parseType : string → Either string ex-tp
  parseKind : string → Either string ex-kd
  parseDefTermOrType : string → Either string ex-def

{-# COMPILE GHC parseStart = CedilleParser.parseTxt #-}
{-# COMPILE GHC parseTerm = CedilleParser.parseTerm #-}
{-# COMPILE GHC parseType = CedilleParser.parseType #-}
{-# COMPILE GHC parseKind = CedilleParser.parseKind #-}
{-# COMPILE GHC parseDefTermOrType = CedilleParser.parseDefTermOrType #-}
