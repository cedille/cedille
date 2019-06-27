module instances where
open import lib public renaming (return to returnᵢₒ; _>>_ to _>>ᵢₒ_; _>>=_ to _>>=ᵢₒ_)
open import functions public


record functor {ℓ ℓ'} (F : Set ℓ → Set ℓ') : Set (lsuc (ℓ ⊔ ℓ')) where
  infixl 2 _<$>_ _<$_
  field
    fmap : ∀ {A B : Set ℓ} → (A → B) → F A → F B

  {-functor-identity-law :
      ∀ {A} (fa : F A) →
        fmap id fa ≡ fa
    functor-composition-law :
      ∀ {A B C} (f : B → C) (g : A → B) (fa : F A) →
        fmap (f ∘ g) fa ≡ fmap f (fmap g fa)-}
  
  _<$>_ = fmap

  _<$_ : ∀ {A B : Set ℓ} → A → F B → F A
  a <$ fb = (λ _ → a) <$> fb

open functor ⦃...⦄ public


record applicative {ℓ ℓ'} (F : Set ℓ → Set ℓ') : Set (lsuc (ℓ ⊔ ℓ')) where
  infixl 2 _<*>_ _<*_ _*>_
  field
    pure : ∀ {A : Set ℓ} → A → F A
    _<*>_ : ∀ {A B : Set ℓ} → F (A → B) → F A → F B
    ⦃ functorF ⦄ : functor F

  {-applicative-identity-law :
      ∀ {A} (v : F A) →
        pure id <*> v ≡ v
    applicative-composition-law :
      ∀ {A B C} (u : F (B → C)) (v : F (A → B)) (w : F A) →
        pure _∘_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
    applicative-homomorphism-law :
      ∀ {A B} (f : A → B) (x : A) →
        pure f <*> pure x ≡ pure (f x)
    applicative-interchange-law :
      ∀ {A B} (u : F (A → B)) (y : A) →
        u <*> pure y ≡ pure (_$ y) <*> u-}
  
  _<*_ : ∀ {A B : Set ℓ} → F A → F B → F A
  fa <* fb = (λ a b → a) <$> fa <*> fb

  _*>_ : ∀ {A B : Set ℓ} → F A → F B → F B
  fa *> fb = (λ a b → b) <$> fa <*> fb

  liftA : ∀ {A B : Set ℓ} → (A → B) → F A → F B
  liftA g fa = pure g <*> fa

  liftA2 : ∀ {A B C : Set ℓ} → (A → B → C) → F A → F B → F C
  liftA2 g fa fb = pure g <*> fa <*> fb

  sequenceA : ∀ {A : Set ℓ} → 𝕃 (F A) → F (𝕃 A)
  sequenceA = foldr (liftA2 _::_) (pure [])

open applicative ⦃...⦄ public


record monad {ℓ ℓ'} (F : Set ℓ → Set ℓ') : Set (lsuc (ℓ ⊔ ℓ')) where
  infixr 2 _>>_ _>>=_ _=<<_ _>=>_ _>>=c_ _>>c_ _>>=?_ _>>=m_ _>>=s_ _>>=e_ _>>≠_ _>≯_ _>>=r_ _>>r_

  field
    return : ∀{A : Set ℓ} → A → F A
    _>>=_ : ∀{A B : Set ℓ} → F A → (A → F B) → F B

  {-monad-left-identity-law :
      ∀ {A B} (a : A) (k : A → F B) →
        return a >>= k ≡ k a
    monad-right-identity-law :
      ∀ {A} (m : F A) →
        m >>= return ≡ m
    monad-associativity-law :
      ∀ {A B C} (m : F A) (k : A → F B) (h : B → F C) →
        m >>= (λ x → k x >>= h) ≡ (m >>= k) >>= h-}

  _>>_ : ∀ {A B : Set ℓ} → F A → F B → F B
  fa >> fb = fa >>= λ _ → fb

  _=<<_ : ∀ {A B : Set ℓ} → (A → F B) → F A → F B
  fab =<< fa = fa >>= fab
  
  _>=>_ : ∀ {A B C : Set ℓ} → (A → F B) → (B → F C) → (A → F C)
  fab >=> fbc = λ a → fab a >>= fbc

  _>>=c_ : ∀ {A B C : Set ℓ} → F (A × B) → (A → B → F C) → F C
  p >>=c f = p >>= λ {(a , b) → f a b}
  
  _>>c_ : ∀ {A B : Set ℓ} → F A → F B → F (A × B)
  fa >>c fb = fa >>= λ a → fb >>= λ b → return (a , b)
  
  _>>=?_ : ∀ {A B : Set ℓ} → maybe (F A) → (maybe A → F B) → F B
  nothing >>=? f = f nothing
  (just a) >>=? f = a >>= (f ∘ just)

  _>>=s_ : ∀ {A B E : Set ℓ} → F (E ⊎ A) → (A → F (E ⊎ B)) → F (E ⊎ B)
  s >>=s f = s >>= λ {(inj₁ e) → return (inj₁ e); (inj₂ a) → f a}

  _>>=e_ : ∀ {A B : Set ℓ} → F (error-t A) → (A → F (error-t B)) → F (error-t B)
  fe? >>=e f = fe? >>= λ {(no-error a) → f a; (yes-error e) → return (yes-error e)}
  
  _>>=m_ : ∀{A B : Set ℓ} → F (maybe A) → (A → F (maybe B)) → F (maybe B)
  m >>=m f = m >>= λ {(just a) → f a; nothing → return nothing}

  _>>≠_  : ∀{A B : Set ℓ} → F A → (A → F B) → F A
  (f₁ >>≠ f₂) = f₁ >>= λ result → f₂ result >> return result

  _>≯_ : ∀{A B : Set ℓ} → F A → F B → F A
  (f₁ >≯ f₂) = f₁ >>= λ result → f₂ >> return result

  _>>=r_ : ∀{A B : Set ℓ} → F A → (A → B) → F B
  a >>=r f = a >>= (return ∘ f)

  _>>r_ : ∀{A B : Set ℓ} → F A → B → F B
  a >>r b = a >> return b
  
  _on-fail_>>=m_ : ∀ {A B : Set ℓ} → F (maybe A) → F B → (A → F B) → F B
  fa? on-fail fb >>=m fab = fa? >>= λ {(just a) → fab a; nothing → fb}

  _on-fail_>>=s_ : ∀ {A B E : Set ℓ} → F (E ⊎ A) → (E → F B) → (A → F B) → F B
  fa+e on-fail feb >>=s fab = fa+e >>= λ {(inj₁ e) → feb e; (inj₂ a) → fab a}
  
  return2 : ∀ {A B : Set ℓ} → A → B → F (A × B)
  return2 a b = return (a , b)
  
  foldrM : ∀ {A B} → (A → F B → F B) → F B → 𝕃 (F A) → F B
  foldrM c n [] = n
  foldrM c n (fa :: fas) = fa >>= λ a → c a (foldrM c n fas)

  foldlM : ∀ {A B} → (A → F B → F B) → F B → 𝕃 (F A) → F B
  foldlM c n [] = n
  foldlM c n (fa :: fas) = fa >>= λ a → foldlM c (c a n) fas
  
  forM_init_use_ : ∀ {A B} → 𝕃 (F A) → F B → (A → F B → F B) → F B
  forM as init b use f = foldrM f b as
  
open monad ⦃...⦄ public

join : ∀ {ℓ}{F : Set ℓ → Set ℓ}{A : Set ℓ} ⦃ _ : monad F ⦄ → F (F A) → F A
join ffa = ffa >>= id

infixr 2 _>>∘_
_>>∘_ : ∀{ℓ}{F : Set ℓ → Set ℓ}{A B : Set ℓ} ⦃ _ : monad F ⦄ → F A → F (A → F B) → F B
a >>∘ f = a >>= λ a → f >>= λ f → f a


--========== Id ==========--
-- Using "id" itself causes Agda to hang when resolving instances, I suspect due
-- to something like endlessly embedding (id (id (id (...)))). So instead we must
-- use a "newtype" for id.

record Id (A : Set) : Set where
  constructor id-in
  field id-out : A
open Id public

instance
  id-functor : functor Id
  id-applicative : applicative Id
  id-monad : monad Id

  fmap ⦃ id-functor ⦄ f = id-in ∘ (f ∘ id-out)

  pure ⦃ id-applicative ⦄ = id-in
  _<*>_ ⦃ id-applicative ⦄ fab fa = id-in (id-out fab (id-out fa))

  return ⦃ id-monad ⦄ = id-in
  _>>=_ ⦃ id-monad ⦄ a f = f (id-out a)


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

  fmap ⦃ IO-functor ⦄ g fa = fa >>=ᵢₒ λ a → returnᵢₒ (g a)

  pure ⦃ IO-applicative ⦄ = returnᵢₒ
  _<*>_ ⦃ IO-applicative ⦄ fab fa = fab >>=ᵢₒ λ ab → fa >>=ᵢₒ λ a → returnᵢₒ (ab a)

  return ⦃ IO-monad ⦄ = returnᵢₒ
  _>>=_ ⦃ IO-monad ⦄ = _>>=ᵢₒ_


--========== ⊎ ==========--

instance
  sum-functor : ∀ {ℓ ℓ'} {E : Set ℓ} → functor {ℓ'} {ℓ ⊔ ℓ'} (E ⊎_)
  sum-applicative : ∀ {ℓ ℓ'} {E : Set ℓ} → applicative {ℓ'} {ℓ ⊔ ℓ'} (E ⊎_)
  sum-monad : ∀ {ℓ ℓ'} {E : Set ℓ} → monad {ℓ'} {ℓ ⊔ ℓ'} (E ⊎_)

  fmap ⦃ sum-functor ⦄ f (inj₁ e) = inj₁ e
  fmap ⦃ sum-functor ⦄ f (inj₂ a) = inj₂ (f a)

  pure ⦃ sum-applicative ⦄ = inj₂
  _<*>_ ⦃ sum-applicative ⦄ sf sa =
    sf >>= λ f →
    sa >>= λ a →
    return (f a)

  return ⦃ sum-monad ⦄ = inj₂
  _>>=_ ⦃ sum-monad ⦄ (inj₁ e) f = inj₁ e
  _>>=_ ⦃ sum-monad ⦄ (inj₂ a) f = f a


--========== maybe ==========--

instance
  maybe-functor : ∀ {ℓ} → functor {ℓ} maybe
  maybe-applicative : ∀ {ℓ} → applicative {ℓ} maybe
  maybe-monad : ∀ {ℓ} → monad {ℓ} maybe
  
  fmap ⦃ maybe-functor ⦄ = maybe-map
  
  pure ⦃ maybe-applicative ⦄ = just
  _<*>_ ⦃ maybe-applicative ⦄ f? a? =
    f? ≫=maybe λ f → a? ≫=maybe (just ∘ f)

  return ⦃ maybe-monad ⦄ = just
  _>>=_ ⦃ maybe-monad ⦄ = _≫=maybe_
  

--========== 𝕃 ==========--

instance
  list-functor : ∀ {ℓ} → functor {ℓ} 𝕃
  list-applicative : ∀ {ℓ} → applicative {ℓ} 𝕃
  list-monad : ∀ {ℓ} → monad {ℓ} 𝕃
  
  fmap ⦃ list-functor ⦄ = map
  
  pure ⦃ list-applicative ⦄ = [_]
  _<*>_ ⦃ list-applicative ⦄ fs as = map (λ {(f , a) → f a}) (zip fs as)

  return ⦃ list-monad ⦄ = [_]
  _>>=_ ⦃ list-monad ⦄ as f = concat (map f as)
