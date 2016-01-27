{- The following code gives the basic idea of division by repeated
   subtraction.  We have to ask Agda not to check termination of this
   function, because it is not structurally terminating.  The versions
   in nat-division.agda and nat-division-wf.agda correct this problem,
   and can be judged by Agda to be terminating. -}

module nat-division-basic where

open import bool
open import eq
open import nat
open import product
open import sum

{-# NO_TERMINATION_CHECK #-}
div : (x d : ℕ) → d =ℕ 0 ≡ ff → ℕ × ℕ
div 0 _ _ = 0 , 0
div x d p with (x < d)
div x d p | tt = 0 , x 
div x d p | ff with div (x ∸ d) d p
div x d p | ff | q , r = suc q , r 

test-div : ℕ × ℕ
test-div = div 17 3 refl
