module type-level where

open import bool
open import level
open import nat

{- multiApply{n} applies a sequence f1, f2, ..., f_n of functions 
   to a starting point a:

   multiApply{n} a f1 f2 ... f_n = f_n (... (f2 (f1 a))) 
-}

multiApplyTh : ℕ → Set → Set lone
multiApplyTh 0 A = Lift A
multiApplyTh (suc n) A = ∀{B : Set} → (A → B) → multiApplyTh n B

multiApplyT : ℕ → Set lone
multiApplyT n = ∀{A : Set} → A → multiApplyTh n A

multiApply-testT = multiApplyT 2

multiApplyh : {A : Set}{n : ℕ} → A → multiApplyTh n A
multiApplyh {n = zero} a = lift a
multiApplyh {n = suc n} a f = multiApplyh{n = n} (f a)

multiApply : {n : ℕ} → multiApplyT n
multiApply{n} = λ{A : Set}(a : A) → multiApplyh{A}{n} a

multiApply-test1 : Lift 𝔹
multiApply-test1 = multiApply{3} 3 (_+_ 3) is-even ~_