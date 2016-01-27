module bool where

open import level

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data 𝔹 : Set where
 tt : 𝔹
 ff : 𝔹

-- this is an alias for Mac users who cannot see blackboard b.
bool : Set
bool = 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  tt  #-}
{-# BUILTIN FALSE ff #-}

{-# COMPILED_DATA 𝔹 Bool True False #-}

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infix  7 ~_
infix 6 _xor_ _nand_
infixr 6 _&&_
infixr 5 _||_ 
infix  4 if_then_else_   if*_then_else_
infixr 4 _imp_ 

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

-- not
~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt


-- and
_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff

-- or
_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then y else z = y
if ff then y else z = z

if*_then_else_ : ∀ {ℓ} {A B : Set ℓ} → (b : 𝔹) → A → B → if b then A else B
if* tt then a else b = a
if* ff then a else b = b

_xor_ : 𝔹 → 𝔹 → 𝔹 
tt xor ff = tt
ff xor tt = tt
tt xor tt = ff
ff xor ff = ff

-- implication
_imp_ : 𝔹 → 𝔹 → 𝔹 
tt imp b2 = b2
ff imp b2 = tt

-- also called the Sheffer stroke
_nand_ : 𝔹 → 𝔹 → 𝔹
tt nand tt = ff
tt nand ff = tt
ff nand tt = tt
ff nand ff = tt

_nor_ : 𝔹 → 𝔹 → 𝔹
x nor y = ~ (x || y)
