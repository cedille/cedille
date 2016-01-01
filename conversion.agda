module conversion where

open import lib

open import cedille-types
open import ctxt
open import syntax-util

{-# NO_TERMINATION_CHECK #-}
conv-term : ctxt → term → term → 𝔹
conv-type : ctxt → type → type → 𝔹
conv-kind : ctxt → kind → kind → 𝔹

conv-term Γ t t' = ff
conv-type Γ t t' = ff
conv-kind Γ k' (KndParens _ k _) = conv-kind Γ k' k
conv-kind Γ (KndParens _ k _) k' = conv-kind Γ k k'
conv-kind Γ (KndVar _ x) k' with ctxt-kind-def Γ x
conv-kind Γ (KndVar _ x) k' | nothing = ff -- we should not have undefined kind variables
conv-kind Γ (KndVar pi x) k' | just k = conv-kind Γ k k'
conv-kind Γ k (KndVar _ x') with ctxt-kind-def Γ x'
conv-kind Γ k (KndVar _ x') | nothing = ff -- we should not have undefined kind variables
conv-kind Γ k (KndVar pi x') | just k' = conv-kind Γ k k'
conv-kind Γ (KndArrow k k₁) (KndArrow k' k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind Γ (KndArrow k k₁) (KndPi _ x (Tkk k') k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind Γ (KndArrow k k₁) _ = ff
conv-kind Γ (KndPi _ x (Tkk k₁) k) (KndArrow k' k'') = conv-kind Γ k₁ k' && conv-kind Γ k k''
conv-kind Γ (KndPi _ x (Tkk k₁) k) (KndPi _ x' (Tkk k') k'') = 
  let Γ' = ctxt-type-def x (TpVar posinfo-gen x') k₁ Γ in
    conv-kind Γ k₁ k' && conv-kind Γ' k k''
conv-kind Γ (KndPi _ x (Tkt t) k) (KndTpArrow t' k'') = conv-type Γ t t' && conv-kind Γ k k''
conv-kind Γ (KndPi _ x (Tkt t) k) (KndPi _ x' (Tkt t') k') = 
  let Γ' = ctxt-term-def x (Var posinfo-gen x') t Γ in
    conv-type Γ t t' && conv-kind Γ' k k'
conv-kind Γ (KndPi _ x (Tkt t) k) _ = ff
conv-kind Γ (KndPi _ x (Tkk k') k) _ = ff
conv-kind Γ (KndTpArrow t k) (KndTpArrow t' k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind Γ (KndTpArrow t k) (KndPi _ x (Tkt t') k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind Γ (KndTpArrow t k) _ = ff
conv-kind Γ (Star x) (Star x') = tt
conv-kind Γ (Star x) _ = ff
