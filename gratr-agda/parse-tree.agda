module parse-tree where

open import lib

record ParseTreeRec : Set lone where
  field
    ParseTreeT : Set
    isParseTree : ParseTreeT → 𝕃 char → string → Set
    ParseTreeToString : ParseTreeT → string


