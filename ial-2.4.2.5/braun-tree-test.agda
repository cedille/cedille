{- modified from a bug report given to me by Ulf Norell, for a 
   previous, incorrect version of bt-remove-min. -}

module braun-tree-test where

open import nat
open import list
open import product
open import sum
open import eq


import braun-tree

open braun-tree nat _<_

test : braun-tree 4
test = bt-node 2 
        (bt-node 3 (bt-node 6 bt-empty bt-empty (inj₁ refl))
            bt-empty (inj₂ refl))
        (bt-node 4 bt-empty bt-empty (inj₁ refl))
        (inj₂ refl)

{-
 

to-list : ∀ {n} → braun-tree n → list nat

to-list {zero} _ = []

to-list {suc _} t with bt-remove-min t

to-list {suc _} t | x , t′ = x :: to-list t′

 

t : braun-tree 5

t = bt-insert 5 (bt-insert 3 (bt-insert 4 (bt-insert 2 (bt-insert 1 bt-empty))))

 

oops : to-list t ≡ (1 :: 2 :: 3 :: 4 :: 5 :: [])
oops = refl
-}
