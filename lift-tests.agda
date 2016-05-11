module lift-tests where

open import lib
open import cedille-types
open import convervsion
open import ctxt
open import lift
open import syntax-util
open import to-string

t0 = Lft posinfo-gen "X" (Parens posinfo-gen (mlam "x" (mlam "y" (mvar "y"))) posinfo-gen)
       (LiftArrow (LiftStar posinfo-gen) (LiftArrow (LiftStar posinfo-gen) (LiftStar posinfo-gen)))

t = TpApp (TpApp t0 (mall "X" (Tkk star) (TpArrow (mtpvar "X") (mtpvar "X")))) (mtpvar "False")
     
s = type-to-string t

s1 = type-to-string (hnf new-ctxt tt t)
