module to-string-tests where

open import lib
open import cedille-types
open import syntax-util
open import to-string

t = mapp (mapp (mvar "plus") (mvar "Z")) (mvar "Z")
s = term-to-string t
