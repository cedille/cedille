module list-thms2 where

open import bool
open import bool-thms
open import bool-thms2
open import functions
open import list
open import list-thms
open import nat
open import nat-thms
open import product-thms
open import logic

list-and-++ : ∀(l1 l2 : 𝕃 𝔹) → list-and (l1 ++ l2) ≡ (list-and l1) && (list-and l2)
list-and-++ [] l2 = refl
list-and-++ (x :: l1) l2 rewrite (list-and-++ l1 l2) | (&&-assoc x (list-and l1) (list-and l2))= refl

list-or-++ : ∀(l1 l2 : 𝕃 𝔹) → list-or (l1 ++ l2) ≡ (list-or l1) || (list-or l2)
list-or-++ [] l2 = refl
list-or-++ (x :: l1) l2 rewrite (list-or-++ l1 l2) | (||-assoc x (list-or l1) (list-or l2))  = refl

++-singleton : ∀{ℓ}{A : Set ℓ}(a : A)(l1 l2 : 𝕃 A) → (l1 ++ [ a ]) ++ l2 ≡ l1 ++ (a :: l2)
++-singleton a l1 [] rewrite ++[] (l1 ++ a :: []) = refl
++-singleton a l1 l2  rewrite (++-assoc l1 [ a ] l2) = refl

list-member-++ : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) → 
                 list-member eq a (l1 ++ l2) ≡ (list-member eq a l1) || (list-member eq a l2)
list-member-++ eq a [] l2 = refl
list-member-++ eq a (x :: l1) l2 with eq a x
list-member-++ eq a (x :: l1) l2 | tt = refl
list-member-++ eq a (x :: l1) l2 | ff rewrite (list-member-++ eq a l1 l2) = refl

list-member-++2 : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) → 
                   list-member eq a l1 ≡ tt → 
                   list-member eq a (l1 ++ l2) ≡ tt
list-member-++2 eq a [] l2 ()
list-member-++2 eq a (x :: l1) l2 p with eq a x
list-member-++2 eq a (x :: l1) l2 p | tt = refl
list-member-++2 eq a (x :: l1) l2 p | ff rewrite (list-member-++2 eq a l1 l2 p) = refl


list-member-++3 : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) →  
                   list-member eq a l2 ≡ tt → 
                   list-member eq a (l1 ++ l2) ≡ tt
list-member-++3 eq a [] l2 p = p
list-member-++3 eq a (x :: l1) l2 p with eq a x
list-member-++3 eq a (x :: l1) l2 p | tt = refl
list-member-++3 eq a (x :: l1) l2 p | ff rewrite (list-member-++3 eq a l1 l2 p) = refl

{-
filter-ff-repeat : ∀{ℓ}{A : Set ℓ}{p : A → 𝔹}{a : A}(n : ℕ) →
                     p a ≡ ff → 
                     filter p (repeat n a) ≡ []
filter-ff-repeat zero p1 = refl
filter-ff-repeat{ℓ}{A}{p0}{a} (suc n) p1 with keep (p0 a)
filter-ff-repeat{ℓ}{A}{p0}{a} (suc n) p1 | tt , y rewrite y = 𝔹-contra (sym p1)
filter-ff-repeat{ℓ}{A}{p0}{a} (suc n) p1 | ff , y rewrite y = filter-ff-repeat {ℓ} {A} {p0} {a} n y
-}

is-empty-distr : ∀{ℓ}{A : Set ℓ} (l1 l2 : 𝕃 A) → is-empty (l1 ++ l2) ≡ (is-empty l1) && (is-empty l2)
is-empty-distr [] l2 = refl
is-empty-distr (x :: l1) l2 = refl

is-empty-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → is-empty l ≡ is-empty (reverse l)
is-empty-reverse [] = refl
is-empty-reverse (x :: xs) rewrite (reverse-++h (x :: []) xs) | (is-empty-distr (reverse-helper [] xs) (x :: []))
                                 | (&&-comm (is-empty (reverse-helper [] xs)) ff) = refl

reverse-length : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → length (reverse l) ≡ length l
reverse-length l = length-reverse-helper [] l

last-distr : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A)(x : A)(p : is-empty l ≡ ff) → last (x :: l) refl ≡ last l p
last-distr [] x ()
last-distr (x :: l) x2 refl = refl

is-empty-[] : ∀{ℓ}{A : Set ℓ} (l : 𝕃 A)(p : is-empty l ≡ tt) → l ≡ []
is-empty-[] [] p = refl
is-empty-[] (x :: l) ()

rev-help-empty : ∀ {ℓ}{A : Set ℓ} (l1 l2 : 𝕃 A) → (p1 : is-empty l2 ≡ ff) → 
                      is-empty (reverse-helper l1 l2) ≡ ff
rev-help-empty l1 [] ()
rev-help-empty l1 (x :: l2) p rewrite reverse-++h (x :: l1) l2 | is-empty-distr (reverse-helper [] l2) (x :: l1)
                                    | (&&-comm (is-empty (reverse-helper [] l2)) ff) = refl

is-empty-revh : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A) → is-empty l ≡ ff → is-empty (reverse-helper h l) ≡ ff
is-empty-revh h l p = rev-help-empty h l p

head-last-reverse-lem : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A)(p : is-empty l ≡ ff) → last l p ≡ head (reverse-helper h l) (is-empty-revh h l p)
head-last-reverse-lem h [] ()
head-last-reverse-lem h (x :: []) p = refl
head-last-reverse-lem h (x :: y :: l) p = head-last-reverse-lem (x :: h) (y :: l) refl

head-last-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A)(p : is-empty l ≡ ff) → last l p ≡ head (reverse l) (rev-help-empty [] l p)
head-last-reverse [] ()
head-last-reverse (x :: l) p with keep (is-empty l)
head-last-reverse (x :: l) refl | tt , b rewrite is-empty-[] l b = refl
head-last-reverse (x :: l) refl | ff , b rewrite (last-distr l x b)  = head-last-reverse-lem (x :: []) l b

reverse-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → reverse (reverse l) ≡ l
reverse-reverse [] = refl
reverse-reverse (x :: l) rewrite (reverse-++h (x :: []) l) | (reverse-++ (reverse-helper [] l) (x  :: [])) | reverse-reverse l = refl

empty++elem : ∀ {ℓ}{A : Set ℓ} (a : A) (l : 𝕃 A) → is-empty ( l ++ [ a ]) ≡ ff
empty++elem a [] = refl
empty++elem a (x :: l) = refl

last-++ : ∀{ℓ}{A : Set ℓ} (a : A) (l : 𝕃 A) → last (l ++ [ a ]) (empty++elem a l) ≡ a
last-++ a [] = refl
last-++ a (x :: l) rewrite last-distr (l ++ [ a ]) x (empty++elem a l) | last-++ a l = refl
