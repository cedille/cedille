module hnf-tests where

open import bool
open import string

open import cedille-types
open import ctxt
open import hnf
open import is-free
open import rename
open import subst
open import syntax-util
open import to-string

S : term
S = mlam "n" (mlam "s" (mlam "z" (mapp (mvar "s") (mapp (mapp (mvar "n") (mvar "s")) (mvar "z")))))

plus : term
plus = mlam "n" (mlam "m" (mapp (mapp (mvar "n") S) (mvar "m")))

zero : term
zero = mlam "s" (mlam "z" (mvar "z"))

one : term
one = mlam "s" (mlam "z" (mapp (mvar "s") (mvar "z")))

plus-one-zero : term
plus-one-zero = mapp (mapp plus one) zero

step : term → term
step t = hnf new-ctxt ff t 

show : term → string
show t = term-to-string t

s2 = show (step (mapp S (mvar "z")))

test = rename-var-if new-ctxt empty-renamectxt "n" "z" (mvar "z")
