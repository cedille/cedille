module conversion where

open import lib

open import cedille-types
open import ctxt
open import syntax-util
open import hnf

{-# NO_TERMINATION_CHECK #-}
conv-term : ctxt → term → term → 𝔹
conv-term-norm : ctxt → term → term → 𝔹
conv-type : ctxt → type → type → 𝔹
conv-type-norm : ctxt → type → type → 𝔹
conv-kind : ctxt → kind → kind → 𝔹
conv-kind-norm : ctxt → kind → kind → 𝔹

conv-term Γ t t' = conv-term-norm Γ (hnf Γ t) (hnf Γ t')
conv-type Γ t t' = conv-type-norm Γ (hnf Γ t) (hnf Γ t')
conv-kind Γ k k' = conv-kind-norm Γ (hnf Γ k) (hnf Γ k')

conv-term-norm Γ (Var _ x) (Var _ x') = x =string x'
conv-term-norm Γ (App t1 m t2) (App t1' m' t2') = conv-term-norm Γ t1 t1' && eq-maybeErased m m' && conv-term Γ t2 t2'
conv-term-norm Γ _ _ = ff

conv-type-norm Γ (TpVar _ x) (TpVar _ x') = x =string x'
conv-type-norm Γ (TpApp t1 t2) (TpApp t1' t2') = conv-type-norm Γ t1 t1' && conv-type Γ t2 t2'
conv-type-norm Γ (TpAppt t1 t2) (TpAppt t1' t2') = conv-type-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ _ _ = ff 

conv-kind-norm Γ (KndVar _ x) (KndVar _ x') = x =string x'
conv-kind-norm Γ (KndArrow k k₁) (KndArrow k' k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) (KndPi _ x (Tkk k') k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) _ = ff
conv-kind-norm Γ (KndPi _ x (Tkk k₁) k) (KndArrow k' k'') = conv-kind Γ k₁ k' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ x (Tkk k₁) k) (KndPi _ x' (Tkk k') k'') = 
  let Γ' = ctxt-type-def x (TpVar posinfo-gen x') k₁ Γ in
    conv-kind Γ k₁ k' && conv-kind Γ' k k''
conv-kind-norm Γ (KndPi _ x (Tkt t) k) (KndTpArrow t' k'') = conv-type Γ t t' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ x (Tkt t) k) (KndPi _ x' (Tkt t') k') = 
  let Γ' = ctxt-term-def x (Var posinfo-gen x') t Γ in
    conv-type Γ t t' && conv-kind Γ' k k'
conv-kind-norm Γ (KndPi _ x (Tkt t) k) _ = ff
conv-kind-norm Γ (KndPi _ x (Tkk k') k) _ = ff
conv-kind-norm Γ (KndTpArrow t k) (KndTpArrow t' k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) (KndPi _ x (Tkt t') k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) _ = ff
conv-kind-norm Γ (Star x) (Star x') = tt
conv-kind-norm Γ (Star x) _ = ff
conv-kind-norm Γ _ _ = ff -- should not happen

