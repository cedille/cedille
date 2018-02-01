{-# OPTIONS --type-in-type #-}
open import Cast
module Examples
  (Nat : ⋆)
  (List : ⋆ → ⋆)
  (len : {A : ⋆} → List A → Nat)
  (plus : Nat → Nat → Nat)
  (Vec : ⋆ → Nat → ⋆)
  (v2l : {A : ⋆} {n : Nat} → Cast' (Vec A n) (List A))
  (l2v : {A : ⋆} → Cast (List A) (λ xs → Vec A (len xs)))
  (v2u : {A : ⋆} {n : Nat} → Cast' (Vec A n) (ι (List A) λ xs → n ≅ len xs))
  (u2v : {A : ⋆} {n : Nat} → Cast' (ι (List A) λ xs → n ≅ len xs) (Vec A n))
  where

VecL : ⋆ → Nat → ⋆
VecL A n = ι (List A) λ xs → n ≅ len xs

appendV2appendL : Cast'
  ({A : ⋆} {n : Nat} → Vec A n → {m : Nat} → Vec A m → Vec A (plus n m))
  ({A : ⋆} → List A → List A → List A)
appendV2appendL =
  copyType λ A →
  allArr2Arr l2v λ n →
  allArr2Arr l2v λ m →
  v2l

assocV2assocL :
  {appendV : {A : ⋆} {n : Nat} → Vec A n → {m : Nat} → Vec A m → Vec A (plus n m)}
  → let appendL = cast' appendV2appendL appendV in
  Cast'
   ({A : ⋆}
    {n : Nat} (xs : Vec A n)
    {m : Nat} (ys : Vec A m)
    {o : Nat} (zs : Vec A o)
    → appendV (appendV xs ys) zs ≅ appendV xs (appendV ys zs))
   ({A : ⋆}
    (xs : List A)
    (ys : List A)
    (zs : List A)
    → appendL (appendL xs ys) zs ≅ appendL xs (appendL ys zs))
assocV2assocL =
  copyType λ A →
  allPi2Pi l2v λ xs →
  allPi2Pi l2v λ ys →
  allPi2Pi l2v λ zs →
  trust -- would be id if agda had untyped equality & casts

appendL2appendV : Cast'
  ({A : ⋆} (xs ys : List A) → VecL A (plus (len xs) (len ys)))
  ({A : ⋆} {n : Nat} → Vec A n → {m : Nat} → Vec A m → Vec A (plus n m))
appendL2appendV =
  copyType λ A →
  pi2allArr v2u λ xs →
  pi2allArr v2u λ ys →
  u2v

