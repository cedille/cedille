module trie-thms where

open import bool
open import bool-thms
open import bool-thms2
open import char
open import eq
open import list
open import list-thms
open import maybe
open import product
open import product-thms
open import sum
open import string
open import trie

trie-lookup-empty-h : ∀ {A} x → trie-lookup-h{A} empty-trie x ≡ nothing
trie-lookup-empty-h [] = refl
trie-lookup-empty-h (_ :: _) = refl

trie-lookup-empty : ∀ {A} x → trie-lookup{A} empty-trie x ≡ nothing
trie-lookup-empty x = trie-lookup-empty-h (string-to-𝕃char x)

trie-cal-insert-nonempty : ∀{A : Set}(ts : cal (trie A))(c : char)(t : trie A) → trie-nonempty t ≡ tt → 
                            trie-cal-nonempty (cal-insert ts c t) ≡ tt
trie-cal-insert-nonempty [] c t p rewrite p = refl
trie-cal-insert-nonempty ((c , t') :: ts) c' t p with c' =char c
trie-cal-insert-nonempty ((c , t') :: ts) c' t p | tt rewrite p = refl
trie-cal-insert-nonempty ((c , t') :: ts) c' t p | ff rewrite (trie-cal-insert-nonempty ts c' t p) = 
  ||-tt (trie-nonempty t')

trie-insert-h-nonempty : ∀{A : Set}(t : trie A)(cs : 𝕃 char)(a : A) → trie-nonempty (trie-insert-h t cs a) ≡ tt
trie-insert-h-nonempty (Node x x₁) [] a = refl
trie-insert-h-nonempty (Node x ts) (c :: cs) a with cal-lookup ts c 
trie-insert-h-nonempty (Node (just x) ts) (c :: cs) a | just t = refl
trie-insert-h-nonempty (Node nothing ts) (c :: cs) a | just t = 
  trie-cal-insert-nonempty ts c (trie-insert-h t cs a) (trie-insert-h-nonempty t cs a)
trie-insert-h-nonempty (Node (just x) ts) (c :: cs) a | nothing = refl
trie-insert-h-nonempty (Node nothing ts) (c :: cs) a | nothing rewrite (trie-insert-h-nonempty empty-trie cs a) = refl

trie-insert-nonempty : ∀{A : Set}(t : trie A)(s : string)(a : A) → trie-nonempty (trie-insert t s a) ≡ tt
trie-insert-nonempty t s a = trie-insert-h-nonempty t (string-to-𝕃char s) a


trie-mappings-h-nonempty : ∀ {A : Set}(t : trie A)(prev-str : 𝕃 char) → 
                             trie-nonempty t ≡ tt → is-empty (trie-mappings-h t prev-str) ≡ ff
trie-cal-mappings-h-nonempty : ∀ {A : Set}(ts : cal (trie A))(prev-str : 𝕃 char) → 
                                 trie-cal-nonempty ts ≡ tt → is-empty (trie-cal-mappings-h ts prev-str) ≡ ff
trie-mappings-h-nonempty (Node (just x) x₁) prev-str _ = refl
trie-mappings-h-nonempty (Node nothing ts) prev-str p = trie-cal-mappings-h-nonempty ts prev-str p
trie-cal-mappings-h-nonempty [] prev-str ()
trie-cal-mappings-h-nonempty ((a , t) :: ts) prev-str p rewrite is-empty-++ (trie-mappings-h t (a :: prev-str)) (trie-cal-mappings-h ts prev-str) with ||-elim{trie-nonempty t} p 
trie-cal-mappings-h-nonempty ((a , t) :: ts) prev-str _ | inj₁ p rewrite trie-mappings-h-nonempty t (a :: prev-str) p = refl
trie-cal-mappings-h-nonempty ((a , t) :: ts) prev-str _ | inj₂ p rewrite trie-cal-mappings-h-nonempty ts prev-str p | &&-ff (is-empty (trie-mappings-h t (a :: prev-str))) = refl

trie-mappings-nonempty : ∀ {A : Set}(t : trie A) → 
                           trie-nonempty t ≡ tt → is-empty (trie-mappings t) ≡ ff
trie-mappings-nonempty t p = trie-mappings-h-nonempty t [] p