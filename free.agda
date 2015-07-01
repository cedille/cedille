module free where

open import lib

open import cedille-types
open import defeq
open import rename
open import subst
open import tpstate

type-var-free-in-type : tpstate → bctxt → renamectxt → var → type → 𝔹
type-var-free-in-type s b r x tp = 
  ~ (eq-type s (bctxt-contains b) r 
        tp 
       (type-subst-type r (bctxt-contains b) (TpVar (tpstate-fresh-var s (bctxt-contains b) x r)) x tp))

-- the stringset tells which variables are bound, and the 𝕃 string is
-- an accumulator argument.
free-varsh : stringset → 𝕃 string → term → 𝕃 string
free-varsh b f (Var x) = if trie-contains b x then f else (x :: f)
free-varsh b f (App t1 t2) = free-varsh b (free-varsh b f t1) t2
free-varsh b f (Lam x t) = free-varsh (stringset-insert b x) f t
free-varsh b f (Parens t) = free-varsh b f t

free-vars : term → 𝕃 string
free-vars t = free-varsh empty-stringset [] t 
