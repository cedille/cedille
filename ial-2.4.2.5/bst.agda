-- binary search trees (not balanced)

open import bool
open import bool-thms2
open import eq
open import maybe
open import product
open import product-thms
open import bool-relations using (transitive ; total)

module bst (A : Set) (_≤A_ : A → A → 𝔹)
           (≤A-trans : transitive _≤A_)
           (≤A-total : total _≤A_) where

open import bool-relations _≤A_ hiding (transitive ; total)
open import minmax _≤A_ ≤A-trans ≤A-total

data bst : A → A → Set where
  bst-leaf : ∀ {l u : A} → l ≤A u ≡ tt → bst l u
  bst-node : ∀ {l l' u' u : A}(d : A) → 
               bst l' d → bst d u' → 
               l ≤A l' ≡ tt → u' ≤A u ≡ tt → 
               bst l u

-- find a node which is isomorphic (_=A_) to d and return it; or else return nothing
bst-search : ∀{l u : A}(d : A) → bst l u → maybe (Σ A (λ d' → d iso𝔹 d' ≡ tt))
bst-search d (bst-leaf _) = nothing
bst-search d (bst-node d' L R _ _) with keep (d ≤A d')
bst-search d (bst-node d' L R _ _) | tt , p1 with keep (d' ≤A d) 
bst-search d (bst-node d' L R _ _) | tt , p1 | tt , p2 = just (d' , iso𝔹-intro p1 p2)
bst-search d (bst-node d' L R _ _) | tt , p1 | ff , p2 = bst-search d L
bst-search d (bst-node d' L R _ _) | ff , p1 = bst-search d R

bst-dec-lb : ∀ {l l' u' : A} → bst l' u' → l ≤A l' ≡ tt → bst l u'
bst-dec-lb (bst-leaf p) q = bst-leaf (≤A-trans q p)
bst-dec-lb (bst-node d L R p1 p2) q = bst-node d L R (≤A-trans q p1) p2

bst-inc-ub : ∀ {l' u' u : A} → bst l' u' → u' ≤A u ≡ tt → bst l' u
bst-inc-ub (bst-leaf p) q = bst-leaf (≤A-trans p q)
bst-inc-ub (bst-node d L R p1 p2) q = bst-node d L R p1 (≤A-trans p2 q)

bst-insert : ∀{l u : A}(d : A) → bst l u → bst (min d l) (max d u)
bst-insert d (bst-leaf p) = bst-node d (bst-leaf ≤A-refl) (bst-leaf ≤A-refl) min-≤1 max-≤1
bst-insert d (bst-node d' L R p1 p2) with keep (d ≤A d') 
bst-insert d (bst-node d' L R p1 p2) | tt , p with bst-insert d L
bst-insert d (bst-node d' L R p1 p2) | tt , p | L' rewrite p = 
  bst-node d' L' (bst-inc-ub R (≤A-trans p2 max-≤2)) (min2-mono p1) ≤A-refl
bst-insert d (bst-node d' L R p1 p2) | ff , p with bst-insert d R
bst-insert d (bst-node d' L R p1 p2) | ff , p | R' rewrite p = 
  bst-node d' (bst-dec-lb L p1) R' min-≤2 (max2-mono p2)

