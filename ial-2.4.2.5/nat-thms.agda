module nat-thms where

open import bool
open import bool-thms
open import bool-thms2
open import eq
open import nat
open import neq
open import product
open import product-thms
open import sum

--------------------------------------------------
-- properties of addition
--------------------------------------------------

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+1 : ∀ (x : ℕ) → x + 1 ≡ suc x
+1 zero = refl
+1 (suc x) rewrite +1 x = refl

+suc : ∀ (x y : ℕ) → x + (suc y) ≡ suc(x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +suc y x | +comm x y = refl

+perm : ∀ (x y z : ℕ) → x + (y + z) ≡ y + (x + z)
+perm x y z rewrite +assoc x y z | +comm x y | sym (+assoc y x z) = refl

+perm2 : ∀ (x y z : ℕ) → (x + y) + z ≡ (x + z) + y
+perm2 x y z rewrite sym (+assoc x y z) | +comm y z | +assoc x z y = refl

+≡0 : ∀ {x y : ℕ} → x + y ≡ 0 → x ≡ 0 ∧ y ≡ 0
+≡0{zero}{zero} p = refl , refl
+≡0{zero}{suc y} ()
+≡0{suc x}{zero} ()
+≡0{suc x}{suc y} ()

--------------------------------------------------
-- properties of multiplication
--------------------------------------------------

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*1 : ∀ {n : ℕ} → n * 1 ≡ n
*1 {0} = refl
*1 {suc n} rewrite *1 {n} = refl

*suc : ∀ (x y : ℕ) → x * (suc y) ≡ x + x * y
*suc zero y = refl
*suc (suc x) y rewrite *suc x y | +assoc y x (x * y) | +assoc x y (x * y) | +comm y x = refl

*distribr : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*distribr zero y z = refl
*distribr (suc x) y z rewrite *distribr x y z = +assoc z (x * z) (y * z) 

*distribl : ∀ (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*distribl 0 y z = refl
*distribl (suc x) y z rewrite *distribl x y z | +assoc (y + z) (x * y) (x * z) | +assoc (y + x * y) z (x * z) | +comm (y + z) (x * y) | +assoc (x * y) y z | +comm (x * y) y = refl

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite *suc y x | *comm x y = refl

*assoc : ∀ (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
*assoc zero y z = refl
*assoc (suc x) y z rewrite *assoc x y z | *distribr y (x * y) z = refl

--------------------------------------------------
-- basic properties of pred
--------------------------------------------------

sucpred : ∀ {x : ℕ} → iszero x ≡ ff → suc (pred x) ≡ x
sucpred{0} ()
sucpred{suc x} p = refl

pred+ : ∀ (x y : ℕ) → iszero x ≡ ff → (pred x) + y ≡ pred (x + y)
pred+ 0 y ()
pred+ (suc x) y p = refl

--------------------------------------------------
-- properties of <, ≤, and =ℕ, iszero
--------------------------------------------------

<-0 : ∀ (x : ℕ) → x < 0 ≡ ff
<-0 0 = refl
<-0 (suc y) = refl

0-≤ : ∀ (x : ℕ) → 0 ≤ x ≡ tt
0-≤ 0 = refl
0-≤ (suc x) = refl

<-drop : ∀ {x y : ℕ} → (x < (suc y) ≡ tt) → x ≡ y ∨ x < y ≡ tt
<-drop {0} {0} p = inj₁ refl
<-drop {suc x} {0} p rewrite <-0 x = 𝔹-contra p
<-drop {0} {suc y} p = inj₂ refl
<-drop {suc x} {suc y} p with <-drop {x} {y} p 
... | inj₁ u rewrite u = inj₁ refl
... | inj₂ u = inj₂ u

=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
=ℕ-refl 0 = refl
=ℕ-refl (suc x) = (=ℕ-refl x)

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ tt → x ≡ y
=ℕ-to-≡ {0} {0} u = refl
=ℕ-to-≡ {suc x} {0} ()
=ℕ-to-≡ {0} {suc y} ()
=ℕ-to-≡ {suc x} {suc y} u rewrite =ℕ-to-≡ {x} {y} u = refl

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ tt
=ℕ-from-≡ {x} refl = =ℕ-refl x

=ℕ-sym : ∀ (x y : ℕ) → (x =ℕ y) ≡ (y =ℕ x)
=ℕ-sym 0 0 = refl
=ℕ-sym 0 (suc y) = refl
=ℕ-sym (suc x) 0 = refl
=ℕ-sym (suc x) (suc y) rewrite =ℕ-sym x y = refl

=ℕ-suc : ∀ (x : ℕ) → suc x =ℕ x ≡ ff
=ℕ-suc 0 = refl
=ℕ-suc (suc x) = =ℕ-suc x

<-suc : ∀ (n : ℕ) → n < suc n ≡ tt
<-suc 0 = refl
<-suc (suc n) rewrite <-suc n = refl

<-suc2 : ∀ (n : ℕ) → suc n < n ≡ ff
<-suc2 0 = refl
<-suc2 (suc n) = <-suc2 n

≤-suc : ∀ (n : ℕ) → n ≤ suc n ≡ tt
≤-suc n rewrite <-suc n = refl

≤-suc2 : ∀ (n : ℕ) → suc n ≤ n ≡ ff
≤-suc2 n rewrite <-suc2 n | =ℕ-suc n = refl

<-push : ∀ {x y : ℕ} → (suc x) < y ≡ tt → Σ ℕ (λ y' → y ≡ (suc y'))
<-push {x} {0} ()
<-push {0} {suc y} p = (y , refl)
<-push {suc x} {suc y} p with <-push {x} {y} p 
... | ( y' , p' ) rewrite p' = (suc y' , refl)

suc-inj : ∀ {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-inj {n} {m} p rewrite (=ℕ-to-≡{n} (=ℕ-from-≡ p)) = refl

<-implies-suc : ∀ {x y : ℕ} → x < y ≡ tt → Σ ℕ λ y' → y ≡ suc y'
<-implies-suc{x}{0} p rewrite <-0 x = 𝔹-contra p
<-implies-suc{y = suc y} p = y , refl

<=ℕff : ∀ (x : ℕ) → 0 < x ≡ tt → x =ℕ 0 ≡ ff
<=ℕff 0 ()
<=ℕff (suc x) p = refl

nonzero< : ∀ {n : ℕ} → iszero n ≡ ff → 0 < n ≡ tt
nonzero<{0} ()
nonzero<{(suc n)} p = refl

iszerosum : ∀ (x y : ℕ) → iszero(x + y) ≡ iszero(x) && iszero(y)
iszerosum 0 y = refl
iszerosum (suc x) y = refl

iszerosum2 : ∀ (x y : ℕ) → iszero x ≡ ff → iszero(x + y) ≡ ff
iszerosum2 0 y ()
iszerosum2 (suc x) y _ = refl

iszeromult : ∀ (x y : ℕ) → iszero x ≡ ff → iszero y ≡ ff → 
               iszero (x * y) ≡ ff
iszeromult zero zero () q 
iszeromult zero (suc y) () q
iszeromult (suc x) zero p ()
iszeromult (suc x) (suc y) p q = refl

<≤ : ∀ {n m : ℕ} → n < m ≡ tt → n ≤ m ≡ tt
<≤ {n}{m} p rewrite p = refl

≤+1 : ∀(x y : ℕ) → x ≤ x + y ≡ tt
≤+1 zero zero = refl
≤+1 zero (suc y) = refl
≤+1 (suc x) zero rewrite +0 x | =ℕ-refl x | ||-tt (x < x) = refl
≤+1 (suc x) (suc y) = ≤+1 x (suc y)

≤+2 : ∀(x y : ℕ) → y ≤ x + y ≡ tt
≤+2 x y rewrite +comm x y = ≤+1 y x

-- a theorem about quotients q, divisors d, and remainders r
÷< : ∀ {d q r x : ℕ} → 1 < d ≡ tt → q * d + r ≡ suc x → q < suc x ≡ tt
÷<{0} () p
÷<{suc 0} () p
÷<{suc (suc d)}{0} u p = refl
÷<{suc (suc d)}{suc q}{r}{0} u ()
÷<{suc (suc d)}{suc q}{r}{suc x} u p with suc-inj{suc (d + q * suc (suc d) + r)}{suc x} p
... | p' rewrite sym (+suc (d + q * suc (suc d)) r) | +comm d (q * suc (suc d)) 
               | sym (+assoc (q * (suc (suc d))) d (suc r)) = ÷<{suc (suc d)}{q}{d + suc r}{x} refl p'  

--------------------------------------------------
-- ordering properties of < and ≤ℕ
--------------------------------------------------

<-irrefl : ∀ (n : ℕ) → n < n ≡ ff
<-irrefl 0 = refl
<-irrefl (suc n) = <-irrefl n

<-asym : ∀ {x y : ℕ} → x < y ≡ tt → y < x ≡ ff
<-asym {0} {0} _ = refl
<-asym {0} {suc y} p = refl
<-asym {suc x}{0} ()
<-asym {suc x}{suc y} p = <-asym {x} {y} p

ℕ-trichotomy𝔹 : ∀ (n m : ℕ) → n < m || n =ℕ m || m < n ≡ tt
ℕ-trichotomy𝔹 0 0 = refl
ℕ-trichotomy𝔹 0 (suc m) = refl
ℕ-trichotomy𝔹 (suc n) 0 = refl
ℕ-trichotomy𝔹 (suc n) (suc m) = ℕ-trichotomy𝔹 n m

ℕ-trichotomy : ∀ (n m : ℕ) → (n < m ≡ tt) ∨ (n =ℕ m ≡ tt) ∨ (m < n ≡ tt)
ℕ-trichotomy n m with ||-split{n < m} (ℕ-trichotomy𝔹 n m)
... | inj₁ p = inj₁ p
... | inj₂ p with ||-split{n =ℕ m} p
... | inj₁ p' = inj₂ (inj₁ p')
... | inj₂ p' = inj₂ (inj₂ p')

<-insert : ∀ {x n m : ℕ} → n ≤ m ≡ tt → (x < n ≡ tt) ∨ (n ≤ x && x ≤ m ≡ tt) ∨ (m < x ≡ tt)
<-insert{x}{n}{m} q with ℕ-trichotomy x n
<-insert{x}{n}{m} q | inj₁ p = inj₁ p
<-insert{x}{n}{m} q | inj₂ (inj₁ p) rewrite (=ℕ-to-≡{x} p) | =ℕ-refl n | ||-tt (n < n) = inj₂ (inj₁ q)
<-insert{x}{n}{m} q | inj₂ (inj₂ p) rewrite p with ℕ-trichotomy x m
<-insert{x}{n}{m} q | inj₂ (inj₂ p) | inj₁ p' rewrite p' = inj₂ (inj₁ refl)
<-insert{x}{n}{m} q | inj₂ (inj₂ p) | inj₂ (inj₁ p') rewrite p' | ||-tt (x < m) = inj₂ (inj₁ refl)
<-insert{x}{n}{m} q | inj₂ (inj₂ p) | inj₂ (inj₂ p') = inj₂ (inj₂ p')

<-insert2 : ∀ {x n m : ℕ} → n ≤ m ≡ tt → (x < n ≡ tt) ∨ (n ≤ x ≡ tt ∧ x ≤ m ≡ tt) ∨ (m < x ≡ tt)
<-insert2{x}{n}{m} p with <-insert{x}{n}{m} p
<-insert2{x}{n}{m} p | inj₁ p' = inj₁ p'
<-insert2{x}{n}{m} p | inj₂ (inj₁ p') with &&-elim {n ≤ x} {x ≤ m} p'
<-insert2{x}{n}{m} p | inj₂ (inj₁ p') | p1 , p2 = inj₂ (inj₁ (p1 , p2))
<-insert2{x}{n}{m} p | inj₂ (inj₂ p') = inj₂ (inj₂ p')

<-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans {x} {0} p1 p2 rewrite <-0 x = 𝔹-contra p1
<-trans {0} {suc y} {0} p1 () 
<-trans {0} {suc y} {suc z} p1 p2 = refl
<-trans {suc x} {suc y} {0} p1 () 
<-trans {suc x} {suc y} {suc z} p1 p2 = <-trans {x} {y} {z} p1 p2

<≤-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y ≤ z ≡ tt → x < z ≡ tt
<≤-trans {x} {y} {z} p1 p2 with ||-split p2
... | inj₁ p' = <-trans{x}  p1 p'
... | inj₂ p' rewrite =ℕ-to-≡ {y} {z} p' = p1

≤<-trans : ∀ {x y z : ℕ} → x ≤ y ≡ tt → y < z ≡ tt → x < z ≡ tt
≤<-trans {x} {y} {z} p1 p2 with ||-split p1
... | inj₁ p' = <-trans{x} p' p2
... | inj₂ p' rewrite =ℕ-to-≡ {x} {y} p' = p2

≤-refl : ∀ (x : ℕ) → x ≤ x ≡ tt
≤-refl 0 = refl
≤-refl (suc x) = ≤-refl x

≤-trans : ∀ {x y z : ℕ} → x ≤ y ≡ tt → y ≤ z ≡ tt → x ≤ z ≡ tt
≤-trans {x} {y} {z} p1 p2 with ||-split p1 | ||-split p2
... | inj₁ p' | inj₁ p'' rewrite <-trans {x} p' p'' = refl
... | inj₂ p' | inj₁ p'' rewrite =ℕ-to-≡ {x} p'  | p'' = refl
... | inj₁ p' | inj₂ p'' rewrite =ℕ-to-≡ {y} p'' | p' = refl
... | inj₂ p' | inj₂ p'' rewrite =ℕ-to-≡ {x} p'  | =ℕ-to-≡ {y} p'' | =ℕ-refl z | ||-tt (z < z) = refl

suc≤ : ∀ {n n' : ℕ} → suc n ≤ suc n' ≡ tt → n ≤ n' ≡ tt
suc≤{n}{n'} p = p

suc≤< : ∀ {n n' : ℕ} → suc n ≤ n' ≡ tt → n < n' ≡ tt
suc≤<{n} p = <≤-trans{n} (<-suc n) p 

suc<< : ∀ {n' n : ℕ} → suc n < n' ≡ tt → n < n' ≡ tt
suc<<{n = n} p = <-trans{n} (<-suc n) p 

<-suc-trans : ∀{x y : ℕ} → x < y ≡ tt → x < suc y ≡ tt
<-suc-trans{0}{0} _ = refl
<-suc-trans{suc x}{0} ()
<-suc-trans{0}{suc y} _ = refl
<-suc-trans{suc x}{suc y} p = <-suc-trans{x}{y} p

≤-suc-trans : ∀{x y : ℕ} → x ≤ y ≡ tt → x ≤ suc y ≡ tt
≤-suc-trans{0}{0} _ = refl
≤-suc-trans{suc x}{0} ()
≤-suc-trans{0}{suc y} _ = refl
≤-suc-trans{suc x}{suc y} p = ≤-suc-trans{x}{y} p

-------------------------------------------------------------
-- more properties relating <, ≤ with arithmetic operations
-------------------------------------------------------------

<+ : ∀ {x y : ℕ} → y =ℕ 0 ≡ ff → x < y + x ≡ tt
<+{y = 0} ()
<+{x}{suc 0} p = <-suc x
<+{x}{suc (suc y)} p = <-trans{x}{(suc y) + x}{suc ((suc y) + x)} (<+{x}{suc y} refl) (<-suc ((suc y) + x))

<+2 : ∀ {x y : ℕ} → x < (suc y) + x ≡ tt
<+2{x}{y} = <+{x}{suc y} refl

<-iter-suc-trans-t-h : (n : ℕ) → (x : ℕ) → (accum : ℕ) → Set
<-iter-suc-trans-t-h 0 x accum = x < accum ≡ tt
<-iter-suc-trans-t-h (suc n) x accum = <-iter-suc-trans-t-h n x (suc accum)

<-iter-suc-trans-t : (n : ℕ) → (x : ℕ) → Set
<-iter-suc-trans-t n x = <-iter-suc-trans-t-h n x (suc x)

<-iter-suc-trans-h : ∀ (n : ℕ) → (x : ℕ) → (accum : ℕ) → x < accum ≡ tt → <-iter-suc-trans-t-h n x accum
<-iter-suc-trans-h 0 x accum p = p
<-iter-suc-trans-h (suc n) x accum p = <-iter-suc-trans-h n x (suc accum) (<-suc-trans{x} p)

<-iter-suc-trans : ∀ (n : ℕ) → (x : ℕ) → <-iter-suc-trans-t n x
<-iter-suc-trans n x = <-iter-suc-trans-h n x (suc x) (<-suc x)

≤0 : ∀ (n : ℕ) → 0 ≤ n ≡ tt
≤0 0 = refl
≤0 (suc n) = refl

≤2* : ∀ (x : ℕ) → x ≤ 2 * x ≡ tt
≤2* 0 = refl
≤2* (suc x) rewrite +suc x (x + 0) | ≤<-trans {x} (≤2* x) (<-suc (2 * x)) = refl

0<+ : ∀ (x y : ℕ) → 0 < y ≡ tt → 0 < x + y ≡ tt
0<+ 0 y p = p
0<+ (suc x) y p = refl

<=ℕff2 : ∀ (x : ℕ) → 1 < x ≡ tt → x =ℕ 0 ≡ ff
<=ℕff2 x p = <=ℕff x (<-trans{0}{1}{x} refl p)

*≤ : ∀(x y : ℕ) → x ≤ x * (suc y) ≡ tt
*≤ zero y = refl
*≤ (suc x) y = ≤-trans {x} (*≤ x y) (≤+2 y (x * suc y))

--------------------------------------------------
-- relationships between ≤ and <
--------------------------------------------------

≤ff : ∀ {x y : ℕ} → x ≤ y ≡ ff → y < x ≡ tt
≤ff{0}{0} ()
≤ff{0}{suc y} ()
≤ff{suc x}{0} _ = refl
≤ff{suc x}{suc y} p rewrite ≤ff {x}{y} p = refl

<ff : ∀ {x y : ℕ} → x < y ≡ ff → y ≤ x ≡ tt
<ff{x}{y} p with ℕ-trichotomy x y
... | inj₁ u rewrite u = 𝔹-contra (sym p)
... | inj₂ (inj₁ u) rewrite (=ℕ-to-≡{x} u) | =ℕ-refl y | ||-tt (y < y) = refl
... | inj₂ (inj₂ u) rewrite u = refl

<-not-=ℕ : ∀{x y : ℕ} → x < y ≡ tt → y =ℕ x ≡ ff
<-not-=ℕ{0}{0} ()
<-not-=ℕ{suc x}{0} ()
<-not-=ℕ{0}{suc y} p = refl
<-not-=ℕ{suc x}{suc y} p = <-not-=ℕ{x}{y} p

<-not-> : ∀{x y : ℕ} → x < y ≡ tt → y < x ≡ ff
<-not->{0}{0} ()
<-not->{suc x}{0} ()
<-not->{0}{suc y} p = refl
<-not->{suc x}{suc y} p = <-not->{x}{y} p

<tt : ∀ {x y : ℕ} → x < y ≡ tt → y ≤ x ≡ ff
<tt{x}{y} p rewrite <-not-=ℕ{x}{y} p | <-not->{x}{y} p = refl

≤-antisym : ∀{x y : ℕ} → x ≤ y ≡ tt → y ≤ x ≡ tt → x ≡ y
≤-antisym{x}{y} p q with ||-split {x < y} p 
≤-antisym{x}{y} p q | inj₁ u rewrite <tt{x} u with q
≤-antisym{x}{y} p q | inj₁ u | ()
≤-antisym{x}{y} p q | inj₂ u = =ℕ-to-≡ u

--------------------------------------------------
-- monotonicity properties of < and ≤ℕ
--------------------------------------------------
<+mono1 : ∀ {z x y : ℕ} → x < y ≡ tt → z + x < z + y ≡ tt
<+mono1{0} p = p
<+mono1{suc z} p = <+mono1{z} p

<+mono2 : ∀ {x y z : ℕ} → x < y ≡ tt → x + z < y + z ≡ tt
<+mono2{x}{y}{z} p rewrite +comm x z | +comm y z | <+mono1{z}{x}{y} p = refl

--------------------------------------------------
-- properties of subtraction
--------------------------------------------------

0∸ : ∀ {x : ℕ} → 0 ∸ x ≡ 0
0∸{0} = refl
0∸{suc x} = refl

∸≤ : ∀ (x y : ℕ) → x ∸ y ≤ x ≡ tt
∸≤ 0 0 = refl
∸≤ (suc x) 0 rewrite (=ℕ-refl x) = ||-tt (x < x)
∸≤ 0 (suc y) = refl
∸≤ (suc x) (suc y) with ||-split{x ∸ y < x}{x ∸ y =ℕ x} (∸≤ x y)
... | inj₁ u rewrite <-trans {x ∸ y} u (<-suc x) = refl
... | inj₂ u rewrite (=ℕ-to-≡ {x ∸ y} u) | <-suc x = refl

∸< : ∀ {x y : ℕ} → x =ℕ 0 ≡ ff → x ∸ (suc y) < x ≡ tt
∸< {0} {y} ()
∸< {suc x} {y} _ with ||-split{x ∸ y < x}{x ∸ y =ℕ x} (∸≤ x y) 
... | inj₁ u = <-trans {x ∸ y} u (<-suc x)
... | inj₂ u rewrite (=ℕ-to-≡ {x ∸ y} u) = <-suc x

∸<1 : ∀ {x y : ℕ} → x ∸ y < suc x ≡ tt
∸<1 {zero} {zero} = refl
∸<1 {zero} {suc y} = refl
∸<1 {suc x} {zero} = <-suc x
∸<1 {suc x} {suc y} = <-trans {x ∸ y}{suc x} (∸<1 {x} {y}) (<-suc x)

+∸1 : ∀ {x y : ℕ} → x < y ≡ tt → x + (y ∸ x) ≡ y
+∸1{0} p = refl
+∸1{suc x}{0} ()
+∸1{suc x}{suc y} p rewrite +∸1{x}{y} p = refl

∸+ : ∀ {x y z : ℕ} → x ∸ (y + z) ≡ (x ∸ y) ∸ z
∸+{x}{0} = refl
∸+{0}{suc y}{z} rewrite 0∸{z} = refl
∸+{suc x}{suc y} = ∸+{x}{y}

∸+2 : ∀ {x y : ℕ} → y ≤ x ≡ tt → (x ∸ y) + y ≡ x
∸+2{0}{0} _ = refl
∸+2{suc x}{0} _ rewrite +0 x = refl
∸+2{0}{suc y} ()
∸+2{suc x}{suc y} p rewrite +suc (x ∸ y) y | ∸+2{x}{y} p = refl

∸eq-swap : ∀ {x y z : ℕ} → y ≤ x ≡ tt → z ≡ x ∸ y → z + y ≡ x
∸eq-swap{x}{y}{z} p q = lem (cong (λ w → w + y) q)
                        where lem : z + y ≡ (x ∸ y) + y → z + y ≡ x
                              lem p' rewrite ∸+2{x}{y} p = p'

<∸ : ∀ {x y : ℕ} → (y < x ≡ tt) → ((x ∸ y =ℕ 0) ≡ ff)
<∸ {0}{y} p with <-0 y 
... | q rewrite p = 𝔹-contra (sym q)
<∸ {suc x}{0} p = refl
<∸ {suc x}{suc y} p = <∸{x}{y} p

<∸suc : ∀ {x y : ℕ} → (y < x ≡ tt) → Σ ℕ (λ n → x ∸ y ≡ suc n)
<∸suc{x}{y} p with keep (x ∸ y)
<∸suc{x}{y} p | 0 , r with <∸{x}{y} p
<∸suc{x}{y} p | 0 , r | q rewrite r with q
<∸suc{x}{y} p | 0 , r | q | ()
<∸suc{x}{y} p | suc n , r = n , r

∸suc : ∀ {x y z : ℕ } → y < x ≡ tt → x ∸ (y + (suc z)) < x ∸ y ≡ tt
∸suc{x}{y}{z} p rewrite ∸+{x}{y}{suc z} = ∸< {x ∸ y} (<∸{x}{y} p)

∸suc2 : ∀ {x y z : ℕ } → y < x ≡ tt → x ∸ ((suc z) + y) < x ∸ y ≡ tt
∸suc2{x}{y}{z} p rewrite +comm (suc z) y = ∸suc{x}{y}{z} p

∸cancel : ∀ (x y z : ℕ) → (x + y) ∸ (x + z) ≡ y ∸ z
∸cancel 0 y z = refl
∸cancel (suc x) y z = ∸cancel x y z

distribr*∸ : ∀ (x y z : ℕ) → (x ∸ y) * z ≡  x * z ∸ y * z
distribr*∸ 0 y z rewrite 0∸{y} | 0∸{y * z} = refl
distribr*∸ (suc x) 0 z = refl
distribr*∸ (suc x) (suc y) z rewrite distribr*∸ x y z | ∸cancel z (x * z) (y * z) = refl

∸≤2 : ∀ (n x y : ℕ) →  x ≤ suc n ≡ tt → y =ℕ 0 ≡ ff → x ∸ y ≤ n ≡ tt
∸≤2 0 0 y p1 p2 rewrite 0∸{y} = refl
∸≤2 0 (suc x) 0 p1 ()
∸≤2 0 (suc 0) (suc y) p1 p2 rewrite 0∸{y}= refl
∸≤2 0 (suc (suc x)) (suc y) () p2
∸≤2 (suc n) 0 y p1 p2 rewrite 0∸{y} = refl
∸≤2 (suc n) (suc x) 0 p1 ()
∸≤2 (suc n) (suc x) (suc 0) p1 p2 = p1
∸≤2 (suc n) (suc x) (suc (suc y)) p1 p2 = ≤-trans{x ∸ suc y}{n}{suc n} (∸≤2 n x (suc y) p1 refl) (≤-suc n)

--------------------------------------------------
-- properties of min, max
--------------------------------------------------
min-forced1 : ∀ {n n' m : ℕ} → n < n' ≡ tt → n ≡ min n' m → n ≡ m
min-forced1{n}{n'}{m} p1 p2 with n' < m 
... | tt rewrite p2 = 𝔹-contra (trans (sym (<-irrefl n')) p1)
... | ff = p2

min-suc : ∀ (n m : ℕ) → min (suc n) (suc m) ≡ suc (min n m)
min-suc n m rewrite (ite-arg suc (n < m) n m) = refl

max-suc : ∀ (n m : ℕ) → max (suc n) (suc m) ≡ suc (max n m)
max-suc n m rewrite (ite-arg suc (n < m) m n) = refl

min-comm : ∀ (n m : ℕ) → min n m ≡ min m n
min-comm n m with ℕ-trichotomy n m
... | inj₁ p rewrite <-asym {n} p | p = refl
... | inj₂ (inj₁ p) rewrite =ℕ-to-≡ {n} p = refl
... | inj₂ (inj₂ p) rewrite <-asym {m} p | p = refl

min-same : ∀ (n : ℕ) → min n n ≡ n
min-same n rewrite <-irrefl n = refl

min-<1 : ∀ {n m : ℕ} → min n m ≤ m ≡ tt
min-<1{0}{0} = refl
min-<1{0}{suc m} = refl
min-<1{suc n}{0} = refl
min-<1{suc n}{suc m} rewrite min-suc n m = min-<1{n}

min-<2 : ∀ {n m : ℕ} → min n m ≤ n ≡ tt
min-<2{0}{0} = refl
min-<2{0}{suc m} = refl
min-<2{suc n}{0} = refl
min-<2{suc n}{suc m} rewrite min-suc n m = min-<2{n}

max-<1 : ∀ {n m : ℕ} → n ≤ max n m ≡ tt
max-<1{0}{0} = refl
max-<1{0}{suc m} = refl
max-<1{suc n}{0} rewrite =ℕ-refl n | ||-tt (n < n) = refl
max-<1{suc n}{suc m} rewrite max-suc n m = max-<1{n}

max-<2 : ∀ {n m : ℕ} → n ≤ max n m ≡ tt
max-<2{0}{0} = refl
max-<2{0}{suc m} = refl
max-<2{suc n}{0} rewrite =ℕ-refl n | ||-tt (n < n) = refl
max-<2{suc n}{suc m} rewrite max-suc n m = max-<2{n}

min-mono1 : ∀ (n n' m : ℕ) → n ≤ n' ≡ tt → min n m ≤ min n' m ≡ tt
min-mono1 n n' m p with ||-split{n < n'} p 
... | inj₂ p' rewrite =ℕ-to-≡ {n} p' | =ℕ-refl (min n' m) | ||-tt ((min n' m) < (min n' m)) = refl
... | inj₁ p' with ℕ-trichotomy n' m
... | inj₁ p'' rewrite <-trans {n} p' p'' | p'' | p' = refl
... | inj₂ (inj₁ p'') rewrite =ℕ-to-≡ {n'} p'' | <-irrefl m = min-<1{n}{m}
... | inj₂ (inj₂ p'') rewrite <-asym {m} p'' with ℕ-trichotomy n m 
... | inj₁ p''' rewrite min-<1{n}{m} = refl
... | inj₂ (inj₁ p''') rewrite =ℕ-to-≡ {n} p''' | <-irrefl m | =ℕ-refl m | ||-tt (m < m) = refl
... | inj₂ (inj₂ p''') rewrite <-asym {m} p''' | =ℕ-refl m | ||-tt (m < m) = refl

min-mono2 : ∀ (n m m' : ℕ) → m ≤ m' ≡ tt → min n m ≤ min n m' ≡ tt
min-mono2 n m m' p rewrite min-comm n m | min-comm n m' = min-mono1 m m' n p

--------------------------------------------------
-- some disequalities
--------------------------------------------------

+≢ : ∀ (x y : ℕ) → x ≢ x + suc y
+≢ 0 y ()
+≢ (suc x) y p with =ℕ-from-≡ {suc x} p
... | q with =ℕ-to-≡ {x} q 
... | r = +≢ x y r

--------------------------------------------------
-- properties of parity
--------------------------------------------------
parity-even : ∀ (x : ℕ) → parity (x * 2) ≡ ff
parity-even 0 = refl
parity-even (suc x) rewrite parity-even x = refl

parity-even2 : ∀ (x : ℕ) → parity (2 * x) ≡ ff
parity-even2 x rewrite *comm 2 x = parity-even x

parity-odd : ∀ (x : ℕ) → parity (x * 2 + 1) ≡ tt
parity-odd 0 = refl
parity-odd (suc x) rewrite parity-odd x = refl

parity-add : ∀ (x y : ℕ) → parity (x + y) ≡ (parity x) xor (parity y)
parity-add 0 y rewrite ff-xor (parity y) = refl
parity-add (suc x) y rewrite parity-add x y | ~-xor-distrb (parity x) (parity y) = refl

parity-mult : ∀ (x y : ℕ) → parity (x * y) ≡ (parity x) && (parity y)
parity-mult 0 y = refl
parity-mult (suc x) y rewrite parity-add y (x * y) | parity-mult x y = xor-distrib-&& (parity y) (parity x)

--------------------------------------------------
-- properties of power
--------------------------------------------------
1-pow : ∀ {n : ℕ} → 1 pow n ≡ 1
1-pow {0} = refl
1-pow {(suc n)} rewrite 1-pow {n} = refl

nonzero-pow : ∀ (x y : ℕ) → x =ℕ 0 ≡ ff → iszero (x pow y) ≡ ff
nonzero-pow x 0 _ = refl
nonzero-pow 0 (suc y) ()
nonzero-pow (suc x) (suc y) p rewrite iszerosum2 (suc x pow y) (x * suc x pow y) (nonzero-pow (suc x) y refl) = refl

pow+ : ∀ (x y z : ℕ) → x pow (y + z) ≡ (x pow y) * (x pow z)
pow+ x 0 z rewrite +0 (x pow z) = refl
pow+ x (suc y) z rewrite pow+ x y z | *assoc x (x pow y) (x pow z) = refl

pow* : ∀ (x y z : ℕ) → x pow (y * z) ≡ (x pow y) pow z
pow* x y 0 rewrite *0 y = refl
pow* x y (suc z) rewrite sym (pow* x y z) | sym (pow+ x y (y * z)) | *comm y (suc z) | *comm y z = refl

--------------------------------------------------
-- properties of factorial
--------------------------------------------------
factorial-nonzero : ∀ (n : ℕ) → iszero (factorial n) ≡ ff
factorial-nonzero zero = refl
factorial-nonzero (suc x) rewrite iszerosum (factorial x) (x * factorial x) | factorial-nonzero x = refl

--------------------------------------------------
-- injectivity properties of addition
--------------------------------------------------
+inj1 : ∀ {x y z : ℕ} → x + y ≡ x + z → y ≡ z
+inj1 {0} {y} {z} p = p
+inj1 {suc x} {y} {z} p = +inj1 {x} {y} {z} (suc-inj p)

+inj2 : ∀ {x y z : ℕ} → x + z ≡ y + z → x ≡ y
+inj2 {x} {y} {z} p rewrite +comm x z | +comm y z = +inj1 {z} {x} {y} p

--------------------------------------------------
-- properties of is-even, is-odd
--------------------------------------------------

even~odd : ∀ (x : ℕ) → is-even x ≡ ~ is-odd x
odd~even : ∀ (x : ℕ) → is-odd x ≡ ~ is-even x
even~odd zero = refl
even~odd (suc x) = odd~even x
odd~even zero = refl
odd~even (suc x) = even~odd x
