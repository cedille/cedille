module resugar where
open import cedille-types
open import general-util
open import syntax-util
open import type-util

{-# TERMINATING #-}
resugar : ∀ {ed} → ⟦ ed ⟧ → ⟦ ed ⟧'
resugar-tk : tpkd → ex-tk

resugar {TERM} (App t t') =
  ExApp (resugar t) ff (resugar t')
resugar {TERM} (AppE t tT) =
  either-else' tT (ExApp (resugar t) tt ∘ resugar) (ExAppTp (resugar t) ∘ resugar)
resugar {TERM} (Beta t t') =
  ExBeta pi-gen (just (PosTm (resugar t) pi-gen)) (just (PosTm (resugar t') pi-gen))
resugar {TERM} (Delta T t) =
  ExDelta pi-gen (just (resugar T)) (resugar t)
resugar {TERM} (Hole pi) =
  ExHole pi
resugar {TERM} (IotaPair t₁ t₂ x Tₓ) =
  ExIotaPair pi-gen (resugar t₁) (resugar t₂) (just (ExGuide pi-gen x (resugar Tₓ))) pi-gen
resugar {TERM} (IotaProj t n) =
  ExIotaProj (resugar t) (if n iff ι1 then "1" else "2") pi-gen
resugar {TERM} (Lam me x tk? t) =
  ExLam pi-gen me pi-gen x (maybe-map resugar-tk tk?) (resugar t)
resugar {TERM} (LetTm me x T? t t') =
  ExLet pi-gen me (ExDefTerm pi-gen x (maybe-map resugar T?) (resugar t)) (resugar t')
resugar {TERM} (LetTp x k T t) =
  ExLet pi-gen tt (ExDefType pi-gen x (resugar k) (resugar T)) (resugar t)
resugar {TERM} (Phi t₌ t₁ t₂) =
  ExPhi pi-gen (resugar t₌) (resugar t₁) (resugar t₂) pi-gen
resugar {TERM} (Rho t₌ x Tₓ t) =
  ExRho pi-gen ff nothing (resugar t₌) (just (ExGuide pi-gen x (resugar Tₓ))) (resugar t)
resugar {TERM} (Sigma t) =
  ExSigma pi-gen (resugar t)
resugar {TERM} (Mu μ t Tₘ? f~ ms) =
  ExMu
    pi-gen
    (either-else' μ (λ t → ExIsMu' (resugar <$> t)) (ExIsMu pi-gen))
    (resugar t)
    (maybe-map resugar Tₘ?)
    pi-gen
    (map (λ {(Case x cas t) → ExCase pi-gen x
      (map (λ {(CaseArg me x) → ExCaseArg me pi-gen x}) cas) (resugar t)}) ms)
    pi-gen
resugar {TERM} (Var x) =
  ExVar pi-gen x

resugar {TYPE} (TpAbs me x tk T) =
  ExTpAbs pi-gen me pi-gen x (resugar-tk tk) (resugar T)
resugar {TYPE} (TpApp T tT) =
  either-else' tT (ExTpAppt (resugar T) ∘ resugar) (ExTpApp (resugar T) ∘ resugar)
resugar {TYPE} (TpEq t₁ t₂) =
  ExTpEq pi-gen (resugar t₁) (resugar t₂) pi-gen
resugar {TYPE} (TpHole pi) =
  ExTpHole pi
resugar {TYPE} (TpIota x T₁ T₂) =
  ExTpIota pi-gen pi-gen x (resugar T₁) (resugar T₂)
resugar {TYPE} (TpLam x tk T) =
  ExTpLam pi-gen pi-gen x (resugar-tk tk) (resugar T)
resugar {TYPE} (TpVar x) =
  ExTpVar pi-gen x

resugar {KIND} (KdAbs x tk k) =
  ExKdAbs pi-gen pi-gen x (resugar-tk tk) (resugar k)
resugar {KIND} (KdHole pi) =
  ExKdHole pi
resugar {KIND} KdStar =
  ExKdStar pi-gen

resugar-tk = either-else (ExTkt ∘ resugar) (ExTkk ∘ resugar)
