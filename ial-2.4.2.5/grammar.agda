open import lib
open import sum

module grammar (form : Set)(_eq_ : form → form → 𝔹)(drop-form : (x y : form) → x ≡ y → x eq y ≡ tt)(rise-form : (x y : form) → x eq y ≡ tt → x ≡ y) where

infix 7 _⇒_

data production : Set where
  _⇒_ : form → 𝕃 (form ⊎ char) → production

record grammar {numprods : ℕ} : Set where
  constructor  _,_
  field
    start : form
    prods : 𝕍 production numprods

open grammar

splice : ℕ → 𝕃 (form ⊎ char) → form → 𝕃 (form ⊎ char) → 𝕃 (form ⊎ char)
splice x [] _ _ = []
splice 0 ((inj₁ s) :: ss) s' ss' with s eq s'
... | tt = ss' ++ ss
... | ff = (inj₁ s) :: ss
splice 0 (x :: ss) s' ss' = x :: ss
splice (suc n) (s :: ss) s' ss' = s :: splice n ss s' ss'

𝕃inj₂ : ∀{ℓ ℓ'}{B : Set ℓ}{A : Set ℓ'} → 𝕃 A → 𝕃 (B ⊎ A)
𝕃inj₂ (x :: xs) = (inj₂ x) :: 𝕃inj₂ xs
𝕃inj₂ [] = []

𝕃inj₁ : ∀{ℓ ℓ'}{B : Set ℓ}{A : Set ℓ'} → 𝕃 A → 𝕃 (A ⊎ B)
𝕃inj₁ (x :: xs) = (inj₁ x) :: 𝕃inj₁ xs
𝕃inj₁ [] = []

data derivation{numprods : ℕ} {g : grammar{numprods}} : 𝕃 (form ⊎ char) → 𝕃 char → Set where
  end : {ss : 𝕃 char} → derivation (𝕃inj₂ ss) ss
  step : ∀ {ss1 ss1' : 𝕃 (form ⊎ char)}{ss2 : 𝕃 char}{s : form}{ss : 𝕃 (form ⊎ char)} → 
           (m n : ℕ) → (p : n < numprods ≡ tt) → 
           nth𝕍 n p (prods g) ≡ (s ⇒ ss) → 
           m < length ss1 ≡ tt →
           splice m ss1 s ss ≡ ss1' → 
           derivation {g = g} ss1' ss2 →
           derivation ss1 ss2

splice-concat : ∀{l1 l2 target final : 𝕃 (form ⊎ char)}{n : ℕ}{slice : form} → splice n l1 slice target ≡ final → splice (n + (length l2)) (l2 ++ l1) slice target ≡ l2 ++ final
splice-concat{l2 = []}{n = n} pr rewrite +0 n = pr
splice-concat{l1}{x :: xs}{n = n} pr rewrite +suc n (length xs) | splice-concat{l1}{l2 = xs} pr = refl

_=form⊎char_ : (x y : form ⊎ char) → 𝔹
_=form⊎char_ = =⊎ _eq_ _=char_

form⊎char-drop : (x y : form ⊎ char) → x ≡ y → x =form⊎char y ≡ tt 
form⊎char-drop = ≡⊎-to-= _eq_ _=char_ drop-form ≡char-to-=

form⊎char-rise : (x y : form ⊎ char) → x =form⊎char y ≡ tt → x ≡ y
form⊎char-rise = =⊎-to-≡ _eq_ _=char_ rise-form =char-to-≡


splice-concat2 : ∀{l1 l2 target final : 𝕃 (form ⊎ char)}{n : ℕ}{slice : form} → splice n l1 slice target ≡ final → n < length l1 ≡ tt → splice n (l1 ++ l2) slice target ≡ final ++ l2
splice-concat2{[]}{n = n} pr1 pr2 rewrite <-0 n = 𝔹-contra pr2
splice-concat2{inj₁ x :: xs}{l2}{target}{n = 0}{slice} pr1 pr2 with x eq slice
...| tt rewrite (sym pr1) | ++[] target | ++-assoc target xs l2 = refl
...| ff rewrite (sym pr1) = refl
splice-concat2{inj₂ x :: xs}{l2}{target}{n = 0}{slice} pr1 pr2 rewrite (sym pr1) = refl
splice-concat2{x :: xs}{l2}{target}{[]}{suc n} pr1 pr2 with pr1 
...| ()
splice-concat2{x :: xs}{l2}{target}{f :: fs}{suc n}{slice} pr1 pr2 with =𝕃-from-≡ _=form⊎char_ form⊎char-drop pr1 
...| s1 rewrite splice-concat2{xs}{l2}{target}{fs}{n}{slice} (≡𝕃-from-={l1 = splice n xs slice target}{fs} _=form⊎char_ form⊎char-rise (&&-snd{x =form⊎char f} s1)) pr2 | form⊎char-rise x f (&&-fst{x =form⊎char f} s1) = refl 

length+ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ length l1 + length l2
length+ [] l2 = refl
length+ (x :: xs) l2 rewrite length+ xs l2 = refl

<-h1 : ∀{x y a : ℕ} → x < y ≡ tt → x + a < y + a ≡ tt
<-h1{x}{y}{0} p rewrite +0 x | +0 y = p
<-h1{x}{y}{suc n} p rewrite +suc y n | +suc x n = <-h1{x}{y}{n} p

<-h2 : ∀{a x y : ℕ} → a < x ≡ tt → a < x + y ≡ tt
<-h2{a}{x}{0} p rewrite +0 x = p
<-h2{a}{x}{suc y} p rewrite +suc x y with <-h2{a}{x}{y} p | <-suc (x + y)
...| pr1 | pr2 = <-trans{a}{x + y}{suc (x + y)} pr1 pr2

length𝕃inj₂ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 A) → length (𝕃inj₂{B = B} l) ≡ length l
length𝕃inj₂{B = B} (x :: xs) rewrite length𝕃inj₂{B = B} xs = refl
length𝕃inj₂ [] = refl

𝕃inj₂++ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l1 l2 : 𝕃 A) → 𝕃inj₂{B = B} (l1 ++ l2) ≡ 𝕃inj₂ l1 ++ 𝕃inj₂ l2
𝕃inj₂++ [] l2 = refl
𝕃inj₂++{B = B} (x :: xs) l2 rewrite 𝕃inj₂++{B = B} xs l2 = refl

infixr 10 _deriv++_

_deriv++_ : {l2 l4 : 𝕃 char}{l1 l3 : 𝕃 (form ⊎ char)}{n : ℕ}{gr : grammar{n}} → derivation{g = gr} l1 l2 → derivation{g = gr} l3 l4 → derivation{g = gr} (l1 ++ l3) (l2 ++ l4)
_deriv++_{l2}{l4} end end rewrite sym (𝕃inj₂++{B = form} l2 l4) = end
_deriv++_{l2}{l4}{l1}{l3} f (step{ss1' = ss1'}{s = s}{ss} a b pr1 pr2 pr3 pr4 next) with <-h1{a}{length l3}{length l1} pr3
...| pr5 rewrite +comm (length l3) (length l1) | (sym (length+ l1 l3)) =  step{ss1 = l1 ++ l3}{l1 ++ ss1'}{l2 ++ l4} (a + (length l1)) b pr1 pr2 pr5 (splice-concat{l3}{l1} pr4) (_deriv++_ f next) 
_deriv++_{l2}{l4}{l1} (step{ss1' = ss1'}{s = s}{ss} a b pr1 pr2 pr3 pr4 next) end with <-h2{a}{length l1}{length (𝕃inj₂{B = form} l4)} pr3
...| pr5 rewrite sym (length+ l1 (𝕃inj₂ l4)) = step{ss1 = l1 ++ 𝕃inj₂ l4}{ss1' ++ 𝕃inj₂ l4}{l2 ++ l4} a b pr1 pr2 pr5 (splice-concat2{l1}{𝕃inj₂ l4} pr4 pr3) (_deriv++_ next end)

