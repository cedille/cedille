module syneq where

open import lib
open import cedille-types
open import ctxt
open import rename
open import syntax-util

{- test exprs in hnf for syntactic equality (we assume that all terms
   that occur in those exprs are already erased).  We also assume we
   are not going to see any iota types -}

eqh : {ed : exprd} → renamectxt → ⟦ ed ⟧ → ⟦ ed ⟧ → 𝔹
eqh-tk : renamectxt → tk → tk → 𝔹
eqh {TERM} ρ (App t1 NotErased t2) (App t1' NotErased t2') = eqh ρ t1 t1' && eqh ρ t2 t2'
eqh {TERM} ρ (Beta _) (Beta _) = tt
eqh {TERM} ρ (Hole _) (Hole _) = tt
eqh {TERM} ρ (Lam _ _ _ x _ t) (Lam _ _ _ x' _ t') = eqh (renamectxt-insert ρ x x') t t'
eqh {TERM} ρ (Var _ x) (Var _ x') = eq-var ρ x x'
eqh {TERM} ρ _ _ = ff
eqh {TYPE} ρ (Abs _ b _ x atk tp) (Abs _ b' _ x' atk' tp') =
  eq-binder b b' && eqh-tk ρ atk atk' && eqh (renamectxt-insert ρ x x') tp tp'
eqh {TYPE} ρ (Lft _ _ X t l) (Lft _ _ X' t' l') = eqh (renamectxt-insert ρ X X') t t' && eqh ρ l l'
eqh {TYPE} ρ (TpApp tp1 tp2) (TpApp tp1' tp2') = eqh ρ tp1 tp1' && eqh ρ tp2 tp2'
eqh {TYPE} ρ (TpAppt tp t) (TpAppt tp' t') = eqh ρ tp tp' && eqh ρ t t'
eqh {TYPE} ρ (TpArrow t1 t2) (TpArrow t1' t2') = eqh ρ t1 t1' && eqh ρ t2 t2'
eqh {TYPE} ρ (TpEq t1 t2) (TpEq t1' t2') = eqh ρ t1 t1' && eqh ρ t2 t2'
eqh {TYPE} ρ (TpLambda _ _ x atk tp) (TpLambda _ _ x' atk' tp') = eqh-tk ρ atk atk' && eqh (renamectxt-insert ρ x x') tp tp'
eqh {TYPE} ρ (TpVar _ x) (TpVar _ x') = eq-var ρ x x'
eqh {TYPE} ρ _ _ = ff
eqh {KIND} ρ (KndArrow k1 k2) (KndArrow k1' k2') = eqh ρ k1 k1' && eqh ρ k2 k2'
eqh {KIND} ρ (KndPi _ _ x atk k) (KndPi _ _ x' atk' k') = eqh-tk ρ atk atk' && eqh (renamectxt-insert ρ x x') k k'
eqh {KIND} ρ (KndTpArrow tp k) (KndTpArrow tp' k') = eqh ρ tp tp' && eqh ρ k k'
eqh {KIND} ρ (KndVar _ x) (KndVar _ y) = eq-var ρ x y
eqh {KIND} ρ (Star _) (Star _) = tt
eqh {KIND} ρ _ _ = ff
eqh {LIFTINGTYPE} ρ (LiftParens _ l _) y = eqh ρ l y
eqh {LIFTINGTYPE} ρ y (LiftParens _ l _) = eqh ρ y l
eqh {LIFTINGTYPE} ρ (LiftArrow l1 l2) (LiftArrow l1' l2') = eqh ρ l1 l1' && eqh ρ l2 l2'
eqh {LIFTINGTYPE} ρ (LiftStar _) (LiftStar _) = tt
eqh {LIFTINGTYPE} ρ _ _ = ff

eqh-tk ρ (Tkk k) (Tkk k') = eqh ρ k k'
eqh-tk ρ (Tkt t) (Tkt t') = eqh ρ t t'
eqh-tk ρ _ _ = ff

eq : {ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧ → 𝔹
eq e1 e2 = eqh empty-renamectxt e1 e2
