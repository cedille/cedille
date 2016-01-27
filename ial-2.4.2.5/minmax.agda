open import bool
open import bool-thms2
open import eq
open import product
open import product-thms
open import bool-relations

module minmax {A : Set} (_≤A_ : A → A → 𝔹)
              (≤A-trans : transitive _≤A_)
              (≤A-total : total _≤A_) where

≤A-refl : reflexive _≤A_ 
≤A-refl = total-reflexive _≤A_ ≤A-total

min : A → A → A
min = λ x y → if x ≤A y then x else y

max : A → A → A
max = λ x y → if x ≤A y then y else x

min-≤1 : ∀{x y : A} → min x y ≤A x ≡ tt
min-≤1{x}{y} with keep (x ≤A y)
min-≤1{x}{y} | tt , p rewrite p = ≤A-refl
min-≤1{x}{y} | ff , p with ≤A-total p 
min-≤1{x}{y} | ff , p | q rewrite p = q

min-≤2 : ∀{x y : A} → min x y ≤A y ≡ tt
min-≤2{x}{y} with keep (x ≤A y)
min-≤2{x}{y} | tt , p = cont p
  where h : x ≤A y ≡ tt → min x y ≡ x
        h p rewrite p = refl
        cont : x ≤A y ≡ tt → min x y ≤A y ≡ tt
        cont p rewrite h p | p = refl

min-≤2{x}{y} | ff , p rewrite p = ≤A-refl

max-≤1 : ∀{x y : A} → x ≤A max x y ≡ tt
max-≤1{x}{y} with keep (x ≤A y)
max-≤1{x}{y} | tt , p = cont p
  where h : x ≤A y ≡ tt → max x y ≡ y
        h p rewrite p = refl
        cont : x ≤A y ≡ tt → x ≤A max x y ≡ tt
        cont p rewrite h p | p = refl
max-≤1{x}{y} | ff , p rewrite p = ≤A-refl

max-≤2 : ∀{x y : A} → y ≤A max x y ≡ tt
max-≤2{x}{y} with keep (x ≤A y)
max-≤2{x}{y} | tt , p rewrite p = ≤A-refl
max-≤2{x}{y} | ff , p with ≤A-total p
max-≤2{x}{y} | ff , p | q rewrite p = q

min1-mono : ∀{x x' y : A} → x ≤A x' ≡ tt → min x y ≤A min x' y ≡ tt
min1-mono{x}{x'}{y} p with keep (x ≤A y) | keep (x' ≤A y)
min1-mono p | tt , q | tt , q' rewrite q | q' = p
min1-mono p | tt , q | ff , q' rewrite q' = min-≤2
min1-mono p | ff , q | tt , q' rewrite ≤A-trans p q' with q 
min1-mono p | ff , q | tt , q' | ()
min1-mono p | ff , q | ff , q' rewrite q | q' = ≤A-refl

min2-mono : ∀{x y y' : A} → y ≤A y' ≡ tt → min x y ≤A min x y' ≡ tt
min2-mono{x}{y}{y'} p with keep (x ≤A y) | keep (x ≤A y') 
min2-mono p | tt , q | tt , q' rewrite q | q' = ≤A-refl
min2-mono p | tt , q | ff , q' rewrite ≤A-trans q p with q'
min2-mono p | tt , q | ff , q' | ()
min2-mono p | ff , q | tt , q' rewrite q' = min-≤1
min2-mono p | ff , q | ff , q' rewrite q | q' = p

max2-mono : ∀{x y y' : A} → y ≤A y' ≡ tt → max x y ≤A max x y' ≡ tt
max2-mono{x}{y}{y'} p with keep (x ≤A y) | keep (x ≤A y')
max2-mono p | tt , q | tt , q' rewrite q | q' = p
max2-mono p | tt , q | ff , q' with ≤A-trans p (≤A-total q') 
max2-mono p | tt , q | ff , q' | q'' rewrite q | q' = q''
max2-mono p | ff , q | tt , q' rewrite q = cont q' 
  where h : ∀{x y' : A} → x ≤A y' ≡ tt → max x y' ≡ y'
        h q' rewrite q' = refl
        cont : ∀{x y' : A} → x ≤A y' ≡ tt → x ≤A max x y' ≡ tt
        cont{x}{y'} q' rewrite h q' = q'

max2-mono p | ff , q | ff , q' rewrite q | q' = ≤A-refl
