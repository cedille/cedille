module parse-tree where

open import ial

record ParseTreeRec : Set lone where
  field
    ParseTreeT : Set
    isParseTree : ParseTreeT → 𝕃 char → string → Set
    ParseTreeToString : ParseTreeT → string
