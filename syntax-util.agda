module syntax-util where

open import lib
open import cedille-types

posinfo-next : ℕ → posinfo → posinfo
posinfo-next n pi with (string-to-ℕ pi)
posinfo-next n pi | just n' = ℕ-to-string (n + n')
posinfo-next n pi | nothing = pi

posinfo-gen : posinfo
posinfo-gen = "generated"
