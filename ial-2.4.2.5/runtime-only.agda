{- In some cases you may want to block certain terms from being
  evaluated by Agda at compile time.  I found I needed to do this
  when generating large terms intended for evaluation at run-time only.
  You can use the runtime-only function for this.  If its first
  argument is tt, then we will use a postulate runtime-identity
  to block Agda's compile-time evaluation.  Otherwise, we will 
  not block compile-time evaluation. -}
module runtime-only where

open import bool

postulate
  runtime-identity : ∀{A : Set} → A → A

{-# COMPILED runtime-identity (\ _ x -> x )   #-}

runtime-only : ∀{A : Set} → 𝔹 → A → A
runtime-only ff = λ x → x
runtime-only tt = runtime-identity