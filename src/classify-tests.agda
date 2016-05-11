module classify-tests where

open import lib
open import classify
open import syntax-util

test = check-beta-inequiv (mlam "a" (mlam "b" (mvar "a"))) (mlam "a" (mlam "b" (mvar "b")))
