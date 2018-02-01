{-# OPTIONS --type-in-type #-}
module Cast where

⋆ = Set
postulate
  _≅_ : {A B : ⋆} → A → B → ⋆
  ι : (A : ⋆) (B : A → ⋆) → ⋆
  Cast : (A : ⋆) → (A → ⋆) → ⋆
  cast : {A : ⋆} {B : A → ⋆} → Cast A B → (a : A) → B a
  trust : {A : ⋆} → A

Cast' : (A B : ⋆) → ⋆
Cast' A B = Cast A (λ _ → B)

cast' : {A B : ⋆} → Cast' A B → A → B
cast' = cast

postulate
  id : {A : ⋆} → Cast' A A

  copyType : {B1 B2 : ⋆ → ⋆}
    → ((A : ⋆) → Cast' (B1 A) (B2 A))
    → Cast' ({A : ⋆} → B1 A) ({A : ⋆} → B2 A)

  allArr2Arr : {A1 : ⋆} {B1 C1 : A1 → ⋆} {A2 B2 : ⋆}
    {c1 : A2 → A1}
    (c2 : Cast A2 (λ a1 → B1 (c1 a1)))
    (c3 : (a1 : A1) → Cast' (C1 a1) B2)
    → Cast' ({a1 : A1} → B1 a1 → C1 a1) (A2 → B2)

  allPi2Pi : {A1 : ⋆} {B1 : A1 → ⋆} {C1 : (a1 : A1) → B1 a1 → ⋆} {A2 : ⋆} {B2 : A2 → ⋆}
    {c1 : A2 → A1}
    (c2 : Cast A2 (λ a1 → B1 (c1 a1)))
    (c3 : (a2 : A2) → Cast' (C1 (c1 a2) (cast c2 a2)) (B2 a2))
    → Cast' ({a1 : A1} (b1 : B1 a1) → C1 a1 b1) ((a2 : A2) → B2 a2)

  pi2allArr : {A1 : ⋆} {B1 : A1 → ⋆} {A2 : ⋆} {B2 : A2 → ⋆} {C2 : A2 → ⋆}
    {c1 : A1 → A2}
    (c2 : {a2 : A2} → Cast' (B2 a2) (ι A1 λ a1 → a2 ≅ c1 a1))
    (c3 : (a1 : A1) → Cast' (B1 a1) (C2 (c1 a1)))
    → Cast' ((a1 : A1) → B1 a1) ({a2 : A2} → B2 a2 → C2 a2)


