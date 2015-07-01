module normalize where

open import lib

open import cedille-types
open import rename
open import subst
open import tpstate

{-# NO_TERMINATION_CHECK #-}
normalize : tpstate → renamectxt → (var → 𝔹) → term → term
normalize s r b (Parens t) = normalize s r b t
normalize s r b (Lam x t) = 
  let x' = rename-away' s b r x in
  (Lam x' (normalize s (renamectxt-insert r x x') b t))
normalize s r b (Var x) with lookup-term-var s (renamectxt-rep r x)
normalize s r b (Var x) | nothing = Var (renamectxt-rep r x)
normalize s r b (Var x) | just t = normalize s r b t
normalize s r b (App t1 t2) with normalize s r b t1
normalize s r b (App t1 t2) | Lam x t1' = 
  let x' = rename-away' s b r x in
  let r' = renamectxt-insert r x x' in
    normalize s r b (term-subst-term r' b (normalize s r b t2) x' t1')
normalize s r b (App t1 t2) | t1' = App t1' (normalize s r b t2)