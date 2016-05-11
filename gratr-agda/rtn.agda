open import lib

module rtn (gratr2-nt : Set) where
     
gratr2-rule : Set
gratr2-rule =  maybe string × maybe string × maybe gratr2-nt × 𝕃 (gratr2-nt ⊎ char)

record gratr2-rtn : Set where
  field
    start : gratr2-nt
    _eq_ : gratr2-nt → gratr2-nt → 𝔹
    gratr2-start : gratr2-nt → 𝕃 gratr2-rule
    gratr2-return : maybe gratr2-nt → 𝕃 gratr2-rule


