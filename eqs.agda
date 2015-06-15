module eqs where

open import lib
open import cedille-types
open import tpstate

eq-kind : tpstate → kind → kind → 𝔹 
eq-lkind : tpstate → lkind → lkind → 𝔹 
eq-bkind : tpstate → bkind → bkind → 𝔹 
eq-kbkind : tpstate → kind → bkind → 𝔹 
eq-kind s k k' = {!!}
eq-lkind s k k' = {!!}
eq-bkind s (KndParens k) k' = eq-kbkind s k k'
eq-bkind s k (KndParens k') = eq-kbkind s k' k
eq-bkind s Star Star = tt
eq-kbkind s k k' = ?