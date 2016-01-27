module bool-to-string where

open import bool
open import string

𝔹-to-string : 𝔹 → string
𝔹-to-string tt = "tt"
𝔹-to-string ff = "ff"