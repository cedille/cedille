module combinators where

open import bool
open import bool-thms2
import closures
open import eq
open import list
open import list-thms
open import nat
open import nat-thms
open import product
open import product-thms
open import sum
open import string
open import termination

data comb : Set where
  S : comb
  K : comb
  app : comb → comb → comb

size : comb → ℕ
size S = 1
size K = 1
size (app a b) = suc (size a + size b)

data _↝_ : comb → comb → Set where
  ↝K : (a b : comb) → (app (app K a) b) ↝ a
  ↝S : (a b c : comb) → (app (app (app S a) b) c) ↝ (app (app a c) (app b c))
  ↝Cong1 : {a a' : comb} (b : comb) → a ↝ a' → (app a b) ↝ (app a' b)
  ↝Cong2 : (a : comb) {b b' : comb} → b ↝ b' → (app a b) ↝ (app a b')

Sfree : comb → 𝔹
Sfree S = ff
Sfree K = tt
Sfree (app a b) = Sfree a && Sfree b

Sfree-↝-size> : ∀{a b : comb} → Sfree a ≡ tt → a ↝ b → size a > size b ≡ tt
Sfree-↝-size> p (↝K a b) = ≤<-trans {size a} (≤+1 (size a) (size b))
                             (<+2 {size a + size b} {2})
Sfree-↝-size> () (↝S a b c)
Sfree-↝-size> p (↝Cong1{a}{a'} b u) with &&-elim{Sfree a} p
Sfree-↝-size> p (↝Cong1{a}{a'} b u) | p1 , _ = <+mono2 {size a'} (Sfree-↝-size> p1 u) 
Sfree-↝-size> p (↝Cong2 a u) with &&-elim{Sfree a} p
Sfree-↝-size> p (↝Cong2 a u) | _ , p2 = <+mono1{size a} (Sfree-↝-size> p2 u)

↝-preserves-Sfree : ∀{a b : comb} → Sfree a ≡ tt → a ↝ b → Sfree b ≡ tt
↝-preserves-Sfree p (↝K a b) = fst (&&-elim p)
↝-preserves-Sfree () (↝S a b c)
↝-preserves-Sfree p (↝Cong1 b u) with &&-elim p
↝-preserves-Sfree p (↝Cong1 b u) | p1 , p2 = &&-intro (↝-preserves-Sfree p1 u) p2
↝-preserves-Sfree p (↝Cong2 a u) with &&-elim{Sfree a} p 
↝-preserves-Sfree p (↝Cong2 a u) | p1 , p2 = &&-intro p1 (↝-preserves-Sfree p2 u)

Sfree-comb : Set
Sfree-comb = Σ comb (λ a → Sfree a ≡ tt)

↝-Sfree-comb : Sfree-comb → Sfree-comb → Set
↝-Sfree-comb (a , _) (b , _) = a ↝ b

size-Sfree-comb : Sfree-comb → ℕ
size-Sfree-comb (a , _) = size a

decrease-size : ∀ {x y : Sfree-comb} → ↝-Sfree-comb x y → size-Sfree-comb x > size-Sfree-comb y ≡ tt
decrease-size{a , u}{b , _} p = Sfree-↝-size> u p

open measure{A = Sfree-comb} ↝-Sfree-comb (λ x y → x > y ≡ tt) size-Sfree-comb decrease-size

measure-decreases : ∀(a : Sfree-comb) → ↓ ↝-Sfree-comb a
measure-decreases a = measure-↓ (↓-> (size-Sfree-comb a))

Sfree-terminatesh : ∀{a : comb}{p : Sfree a ≡ tt} → ↓ ↝-Sfree-comb (a , p) →  ↓ _↝_ a
Sfree-terminatesh{a}{p} (pf↓ f) = pf↓ h
  where h : {y : comb} → a ↝ y → ↓ _↝_ y
        h{y} u = Sfree-terminatesh (f {y , ↝-preserves-Sfree p u} u)  

Sfree-terminates : ∀(a : comb) → Sfree a ≡ tt → ↓ _↝_ a
Sfree-terminates a p = Sfree-terminatesh (measure-decreases (a , p))

data varcomb : Set where
  S : varcomb 
  K : varcomb 
  app : varcomb → varcomb → varcomb 
  var : (s : string) → varcomb 

λ* : (s : string) → varcomb → varcomb 
λ* s S = app K S
λ* s K = app K K
λ* s (app c1 c2) = app (app S (λ* s c1)) (λ* s c2)
λ* s (var s') = if (s =string s') then (app (app S K) K) else (app K (var s'))

subst : varcomb → string → varcomb → varcomb
subst c s S = S
subst c s K = K
subst c s (app c1 c2) = app (subst c s c1) (subst c s c2)
subst c s (var s') = if (s =string s') then c else var s'

data _↝vc_ : varcomb → varcomb → Set where
  ↝K : (a b : varcomb) → (app (app K a) b) ↝vc a
  ↝S : (a b c : varcomb) → (app (app (app S a) b) c) ↝vc (app (app a c) (app b c))
  ↝Cong1 : {a a' : varcomb} (b : varcomb) → a ↝vc a' → (app a b) ↝vc (app a' b)
  ↝Cong2 : (a : varcomb) {b b' : varcomb} → b ↝vc b' → (app a b) ↝vc (app a b')

open closures.basics _↝vc_

_↝vc+_ : varcomb → varcomb → Set
_↝vc+_ = tc 

id↝ : ∀ (a : varcomb) → app (app (app S K) K) a ↝vc+ a
id↝ a = (tc-trans (tc-step (↝S K K a)) (tc-step (↝K a (app K a))))

trans-Cong1 : ∀{a a' : varcomb} (b : varcomb) → a ↝vc+ a' → (app a b) ↝vc+ (app a' b)
trans-Cong1 b (tc-trans d1 d2) = (tc-trans (trans-Cong1 b d1) (trans-Cong1 b d2))
trans-Cong1 b (tc-step d) = tc-step (↝Cong1 b d)

trans-Cong2 : ∀(a : varcomb) {b b' : varcomb} → b ↝vc+ b' → (app a b) ↝vc+ (app a b')
trans-Cong2 a (tc-trans d1 d2) = (tc-trans (trans-Cong2 a d1) (trans-Cong2 a d2))
trans-Cong2 a (tc-step d) = tc-step (↝Cong2 a d)

contains-var : string → varcomb → 𝔹
contains-var s S = ff
contains-var s K = ff
contains-var s (app c1 c2) = contains-var s c1 || contains-var s c2
contains-var s (var s') = s =string s'

λ*-binds : ∀(s : string)(v : varcomb) → contains-var s (λ* s v) ≡ ff
λ*-binds s S = refl
λ*-binds s K = refl
λ*-binds s (app c1 c2) rewrite λ*-binds s c1 | λ*-binds s c2 = refl
λ*-binds s (var s') with keep (s =string s')
λ*-binds s (var s') | tt , p rewrite p = refl
λ*-binds s (var s') | ff , p = cont p 
  where h : s =string s' ≡ ff → _≡_{A = varcomb} (if (s =string s') then app (app S K) K else app K (var s')) (app K (var s'))
        h p rewrite p = refl
        cont : s =string s' ≡ ff → contains-var s (if s =string s' then app (app S K) K else app K (var s')) ≡ ff
        cont p rewrite h p = p

λ*-↝ : ∀ (v1 v2 : varcomb)(s : string) → (app (λ* s v1) v2) ↝vc+ (subst v2 s v1)
λ*-↝ S v2 s = tc-step (↝K S v2)
λ*-↝ K v2 s = tc-step (↝K K v2)
λ*-↝ (app c1 c2) v2 s = 
  (tc-trans (tc-step (↝S (λ* s c1) (λ* s c2) v2))
  (tc-trans (trans-Cong1 (app (λ* s c2) v2) (λ*-↝ c1 v2 s))
    (trans-Cong2 (subst v2 s c1) (λ*-↝ c2 v2 s))))
λ*-↝ (var s') v2 s with s =string s'
λ*-↝ (var s') v2 s | tt = id↝ v2
λ*-↝ (var s') v2 s | ff = tc-step (↝K (var s') v2)
