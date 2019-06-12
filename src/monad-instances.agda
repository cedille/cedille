module monad-instances where
open import lib
open import general-util


--========== id ==========--

instance
  id-functor : functor id
  id-applicative : applicative id
  id-monad : monad id

  fmap ⦃ id-functor ⦄ = id
--  functor-identity-law ⦃ id-functor ⦄ a = refl
--  functor-composition-law ⦃ id-functor ⦄ f g a = refl

  pure ⦃ id-applicative ⦄ = id
  _<*>_ ⦃ id-applicative ⦄ fab fa = fab fa
--  applicative-identity-law ⦃ id-applicative ⦄ v = refl
--  applicative-composition-law ⦃ id-applicative ⦄ u v w = refl
--  applicative-homomorphism-law ⦃ id-applicative ⦄ f x = refl
--  applicative-interchange-law ⦃ id-applicative ⦄ u y = refl

  returnM ⦃ id-monad ⦄ = id
  _≫=_ ⦃ id-monad ⦄ a f = f a
--  monad-left-identity-law ⦃ id-monad ⦄ a k = refl
--  monad-right-identity-law ⦃ id-monad ⦄ m = refl
--  monad-associativity-law ⦃ id-monad ⦄ m k h = refl



--========== IO ==========--

instance
  IO-functor : functor IO
  IO-applicative : applicative IO
  IO-monad : monad IO

{-
postulate
  IO-functor-identity-law :
    ∀ {A} →
      fmap ⦃ IO-functor ⦄ {A} id ≡ id
  IO-functor-composition-law :
    ∀ {A B C} (f : B → C) (g : A → B) →
      fmap (f ∘ g) ≡ fmap f ∘ fmap g

  IO-applicative-identity-law :
    ∀ {A} (v : IO A) →
      pure ⦃ IO-applicative ⦄ id <*> v ≡ v
  IO-applicative-composition-law :
    ∀ {A B C} (u : IO (B → C)) (v : IO (A → B)) (w : IO A) →
      pure ⦃ IO-applicative ⦄ _∘_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
  IO-applicative-homomorphism-law :
    ∀ {A B} (f : A → B) (x : A) →
      pure ⦃ IO-applicative ⦄ f <*> pure x ≡ pure (f x)
  IO-applicative-interchange-law :
    ∀ {A B} (u : IO (A → B)) (y : A) →
      u <*> pure y ≡ pure ⦃ IO-applicative ⦄ (_$ y) <*> u

  IO-monad-left-identity-law :
    ∀ {A B} (a : A) (k : A → IO B) →
      (return a >>= k) ≡ k a
  IO-monad-right-identity-law :
    ∀ {A} (m : IO A) →
      (m >>= return) ≡ m
  IO-monad-associativity-law :
    ∀ {A B C} (m : IO A) (k : A → IO B) (h : B → IO C) →
      (m >>= (λ x → k x >>= h)) ≡ ((m >>= k) >>= h)
-}

instance
  fmap ⦃ IO-functor ⦄ g fa = fa >>= λ a → return (g a)
--  functor-identity-law ⦃ IO-functor ⦄ = IO-functor-identity-law
--  functor-composition-law ⦃ IO-functor ⦄ = IO-functor-composition-law

  pure ⦃ IO-applicative ⦄ = return
  _<*>_ ⦃ IO-applicative ⦄ fab fa = fab >>= λ ab → fa >>= λ a → return (ab a)
--  applicative-identity-law ⦃ IO-applicative ⦄ = IO-applicative-identity-law
--  applicative-composition-law ⦃ IO-applicative ⦄ = IO-applicative-composition-law
--  applicative-homomorphism-law ⦃ IO-applicative ⦄ = IO-applicative-homomorphism-law
--  applicative-interchange-law ⦃ IO-applicative ⦄ = IO-applicative-interchange-law

  returnM ⦃ IO-monad ⦄ = return
  _≫=_ ⦃ IO-monad ⦄ = _>>=_
--  monad-left-identity-law ⦃ IO-monad ⦄ = IO-monad-left-identity-law
--  monad-right-identity-law ⦃ IO-monad ⦄ = IO-monad-right-identity-law
--  monad-associativity-law ⦃ IO-monad ⦄ = IO-monad-associativity-law
