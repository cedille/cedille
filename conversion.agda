module conversion where

open import lib

open import cedille-types
open import ctxt
open import hnf
open import syntax-util
open import to-string

{-# NO_TERMINATION_CHECK #-}
conv-term : ctxt → term → term → 𝔹
conv-term-norm : ctxt → term → term → 𝔹
conv-type : ctxt → type → type → 𝔹
conv-type-norm : ctxt → type → type → 𝔹
conv-kind : ctxt → kind → kind → 𝔹
conv-kind-norm : ctxt → kind → kind → 𝔹
conv-tk : ctxt → tk → tk → 𝔹

conv-term Γ t t' = conv-term-norm Γ (hnf Γ ff t) (hnf Γ ff t')

conv-type Γ t t' with hnf Γ ff t | hnf Γ ff t'
conv-type Γ _ _ | TpVar pi x | TpVar pi' x' with x =string x'
conv-type Γ _ _ | TpVar pi x | TpVar pi' x' | tt = tt
conv-type Γ _ _ | TpVar pi x | TpVar pi' x' | ff = conv-type-norm Γ (hnf Γ tt (TpVar pi x)) (hnf Γ tt (TpVar pi' x'))
conv-type Γ _ _ | t | t' = conv-type-norm Γ t t'

conv-kind Γ k k' = conv-kind-norm Γ (hnf Γ ff k) (hnf Γ ff k')

conv-term-norm Γ (Var _ x) (Var _ x') = x =string x'
-- hnf implements erasure for terms, so we can ignore some subterms for App and Lam cases below
conv-term-norm Γ (App t1 m t2) (App t1' m' t2') = conv-term-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-term-norm Γ (Lam _ l _ x oc t) (Lam _ l' _ x' oc' t') = conv-term (ctxt-rename x x' Γ) t t'
conv-term-norm Γ (Hole _) _ = tt
conv-term-norm Γ _ (Hole _) = tt
conv-term-norm Γ _ _ = ff

conv-type-norm Γ (TpVar _ x) (TpVar _ x') = x =string x'
conv-type-norm Γ (TpApp t1 t2) (TpApp t1' t2') = conv-type-norm Γ t1 t1' && conv-type Γ t2 t2'
conv-type-norm Γ (TpAppt t1 t2) (TpAppt t1' t2') = conv-type-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (Abs _ b _ x atk tp) (Abs _ b' _ x' atk' tp') = 
  eq-binder b b' && conv-tk Γ atk atk' && conv-type (ctxt-rename x x' Γ) tp tp'
conv-type-norm Γ (TpArrow tp1 tp2) (TpArrow tp1' tp2') = conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (TpArrow tp1 tp2) (Abs _ Pi _ _ (Tkt tp1') tp2') = conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (Abs _ Pi _ _ (Tkt tp1) tp2) (TpArrow tp1' tp2') = conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ _ _ = ff 

{- even though hnf turns Pi-kinds where the variable is not free in the body into arrow kinds,
   we still need to check off-cases, because normalizing the body of a kind could cause the
   bound variable to be erased (hence allowing it to match an arrow kind). -}
conv-kind-norm Γ (KndVar _ x) (KndVar _ x') = x =string x'
conv-kind-norm Γ (KndArrow k k₁) (KndArrow k' k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) (KndPi _ _ x (Tkk k') k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) _ = ff
conv-kind-norm Γ (KndPi _ _ x (Tkk k₁) k) (KndArrow k' k'') = conv-kind Γ k₁ k' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ _ x atk k) (KndPi _ _ x' atk' k'') = 
  let Γ' = ctxt-tk-def x x' atk Γ in
    conv-tk Γ atk atk' && conv-kind Γ' k k''
conv-kind-norm Γ (KndPi _ _ x (Tkt t) k) (KndTpArrow t' k'') = conv-type Γ t t' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ _ x (Tkt t) k) _ = ff
conv-kind-norm Γ (KndPi _ _ x (Tkk k') k) _ = ff
conv-kind-norm Γ (KndTpArrow t k) (KndTpArrow t' k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) (KndPi _ _ x (Tkt t') k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) _ = ff
conv-kind-norm Γ (Star x) (Star x') = tt
conv-kind-norm Γ (Star x) _ = ff
conv-kind-norm Γ _ _ = ff -- should not happen, since the kinds are in hnf

conv-tk Γ (Tkk k) (Tkk k') = conv-kind Γ k k'
conv-tk Γ (Tkt t) (Tkt t') = conv-type Γ t t'
conv-tk Γ _ _ = ff

