open import bool

module braun-tree{ℓ} (A : Set ℓ) (_<A_ : A → A → 𝔹) where

open import bool-thms
open import eq
open import list
open import nat
open import nat-thms
open import product
open import sum

-- the index n is the size of the tree (number of elements of type A)
data braun-tree : (n : ℕ) → Set ℓ where
  bt-empty : braun-tree 0
  bt-node : ∀ {n m : ℕ} → 
            A → braun-tree n → braun-tree m → 
            n ≡ m ∨ n ≡ suc m → 
            braun-tree (suc (n + m))


{- we will keep smaller (_<A_) elements closer to the root of the Braun tree as we insert -}
bt-insert : ∀ {n : ℕ} → A → braun-tree n → braun-tree (suc n)

bt-insert a bt-empty = bt-node a bt-empty bt-empty (inj₁ refl)

bt-insert a (bt-node{n}{m} a' l r p) 
  rewrite +comm n m with p | if a <A a' then (a , a') else (a' , a)
bt-insert a (bt-node{n}{m} a' l r _) | inj₁ p | (a1 , a2) 
  rewrite p = (bt-node a1 (bt-insert a2 r) l (inj₂ refl))
bt-insert a (bt-node{n}{m} a' l r _) | inj₂ p | (a1 , a2) = 
  (bt-node a1 (bt-insert a2 r) l (inj₁ (sym p)))

bt-replace-min : ∀{n : ℕ} → A → braun-tree (suc n) → braun-tree (suc n)
bt-replace-min a (bt-node _ bt-empty bt-empty u) = (bt-node a bt-empty bt-empty u)
bt-replace-min a (bt-node _ bt-empty (bt-node _ _ _ _) (inj₁ ()))
bt-replace-min a (bt-node _ bt-empty (bt-node _ _ _ _) (inj₂ ()))
bt-replace-min a (bt-node _ (bt-node _ _ _ _) bt-empty (inj₁ ()))
bt-replace-min a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) with a <A x
bt-replace-min a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) | tt = (bt-node a (bt-node x l r u) bt-empty (inj₂ y))
bt-replace-min a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) | ff = 
 (bt-node x (bt-replace-min a (bt-node x l r u)) bt-empty (inj₂ y))
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) with a <A x && a <A x' 
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | tt = 
 (bt-node a (bt-node x l r u) (bt-node x' l' r' u') v)
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff with x <A x'  
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff | tt = 
 (bt-node x (bt-replace-min a (bt-node x l r u)) (bt-node x' l' r' u') v)
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff | ff = 
 (bt-node x' (bt-node x l r u) (bt-replace-min a (bt-node x' l' r' u')) v)

{- thanks to Matías Giovannini for the excellent post
     http://alaska-kamtchatka.blogspot.com/2010/02/braun-trees.html
   explaining how to do delete -}
bt-delete-min : ∀ {p : ℕ} → braun-tree (suc p) → braun-tree p
bt-delete-min (bt-node a bt-empty bt-empty u) = bt-empty
bt-delete-min (bt-node a bt-empty (bt-node _ _ _ _) (inj₁ ()))
bt-delete-min (bt-node a bt-empty (bt-node _ _ _ _) (inj₂ ()))
bt-delete-min (bt-node a (bt-node{n'}{m'} a' l' r' u') bt-empty u) rewrite +0 (n' + m') = bt-node a' l' r' u'
bt-delete-min (bt-node a
                (bt-node{n}{m} x l1 r1 u1)
                (bt-node{n'}{m'} x' l2 r2 u2) u) 
  rewrite +suc(n + m)(n' + m') | +suc n (m + (n' + m')) 
        | +comm(n + m)(n' + m') = 
  if (x <A x') then
    (bt-node x (bt-node x' l2 r2 u2)
      (bt-delete-min (bt-node x l1 r1 u1)) (lem{n}{m}{n'}{m'} u))
  else
    (bt-node x' (bt-replace-min x (bt-node x' l2 r2 u2))
      (bt-delete-min (bt-node x l1 r1 u1)) (lem{n}{m}{n'}{m'} u))
  where lem : {n m n' m' : ℕ} → suc (n + m) ≡ suc (n' + m') ∨ suc (n + m) ≡ suc (suc (n' + m')) → 
              suc (n' + m') ≡ n + m ∨ suc (n' + m') ≡ suc (n + m)
        lem{n}{m}{n'}{m'} (inj₁ x) = inj₂ (sym x)
        lem (inj₂ y) = inj₁ (sym (suc-inj y))

bt-remove-min : ∀ {p : ℕ} → braun-tree (suc p) → A × braun-tree p
bt-remove-min (bt-node a l r u) = a , bt-delete-min (bt-node a l r u)

----------------------------------------------------------------------
-- this version stores data at the leaves instead of at the nodes
----------------------------------------------------------------------
data braun-tree' : (n : ℕ) → Set ℓ where
  bt'-leaf : A → braun-tree' 1
  bt'-node : ∀ {n m : ℕ} → 
            braun-tree' n → braun-tree' m → 
            n =ℕ m ≡ tt ⊎ n =ℕ m + 1 ≡ tt → 
            braun-tree' (n + m)

bt'-insert : ∀ {n : ℕ} → A → braun-tree' n → braun-tree' (suc n)
bt'-insert a (bt'-leaf a') = bt'-node (bt'-leaf a) (bt'-leaf a') (inj₁ refl)
bt'-insert a (bt'-node{n}{m} l r p) rewrite +comm n m with p 
bt'-insert a (bt'-node{n}{m} l r p) | inj₁ p' rewrite =ℕ-to-≡{n} p' = (bt'-node (bt'-insert a r) l (inj₂ lem))
  where lem : suc m =ℕ m + 1 ≡ tt
        lem rewrite +comm m 1 = =ℕ-refl m 
bt'-insert a (bt'-node{n}{m} l r p) | inj₂ p' = (bt'-node (bt'-insert a r) l (inj₁ (lem n m p')))
  where lem : ∀ n m → n =ℕ m + 1 ≡ tt → suc m =ℕ n ≡ tt
        lem n m p' rewrite =ℕ-to-≡{n} p' | +comm m 1 = =ℕ-refl m
  
𝕃-to-braun-tree' : A → (l : 𝕃 A) → braun-tree' (suc (length l))
𝕃-to-braun-tree' a [] = bt'-leaf a
𝕃-to-braun-tree' a (a' :: as) = bt'-insert a (𝕃-to-braun-tree' a' as)
