module free-vars where
open import cedille-types
open import syntax-util
open import general-util
open import type-util

infixr 7 _++ₛ_
_++ₛ_ : stringset → stringset → stringset
s₁ ++ₛ s₂ = stringset-insert* s₂ (stringset-strings s₁)

stringset-single : string → stringset
stringset-single = flip trie-single triv

{-# TERMINATING #-}
free-vars : ∀ {ed} → ⟦ ed ⟧ → stringset
free-vars? : ∀ {ed} → maybe ⟦ ed ⟧ → stringset
free-vars-args : args → stringset
free-vars-arg : arg → stringset
free-vars-cases : cases → stringset
free-vars-case : case → stringset
free-vars-tk : tpkd → stringset
free-vars-tT : tmtp → stringset

free-vars-tk = free-vars -tk'_
free-vars-tT = free-vars -tT'_

free-vars? = maybe-else empty-stringset free-vars

free-vars {TERM} (App t t') = free-vars t ++ₛ free-vars t'
free-vars {TERM} (AppE t tT) = free-vars t ++ₛ free-vars -tT' tT
free-vars {TERM} (Beta t t') = free-vars t ++ₛ free-vars t'
free-vars {TERM} (Delta b? T t) = free-vars? (fst <$> b?) ++ₛ free-vars? (snd <$> b?) ++ₛ free-vars T ++ₛ free-vars t
free-vars {TERM} (Hole pi) = empty-stringset
free-vars {TERM} (IotaPair t t' x T) = free-vars t ++ₛ free-vars t' ++ₛ stringset-remove (free-vars T) x
free-vars {TERM} (IotaProj t n) = free-vars t
free-vars {TERM} (Lam me x tk t) = maybe-else empty-stringset (free-vars-tk) tk ++ₛ stringset-remove (free-vars t) x
free-vars {TERM} (LetTm me x T? t t') = free-vars? T? ++ₛ free-vars t ++ₛ stringset-remove (free-vars t') x
free-vars {TERM} (LetTp x k T t) = free-vars k ++ₛ free-vars T ++ₛ stringset-remove (free-vars t) x
free-vars {TERM} (Phi tₑ t₁ t₂) = free-vars tₑ ++ₛ free-vars t₁ ++ₛ free-vars t₂
free-vars {TERM} (Rho t x T t') = free-vars t ++ₛ stringset-remove (free-vars T) x ++ₛ free-vars t'
free-vars {TERM} (VarSigma t) = free-vars t
free-vars {TERM} (Mu v t T t~ cs) = free-vars t ++ₛ free-vars? T ++ₛ stringset-remove (free-vars-cases cs) v
free-vars {TERM} (Sigma mt t T t~ cs) = free-vars t ++ₛ free-vars? mt ++ₛ free-vars? T ++ₛ free-vars-cases cs
free-vars {TERM} (Var x) = stringset-single x
free-vars {TYPE} (TpAbs me x tk T) = free-vars-tk tk ++ₛ stringset-remove (free-vars T) x
free-vars {TYPE} (TpIota x T₁ T₂) = free-vars T₁ ++ₛ stringset-remove (free-vars T₂) x
free-vars {TYPE} (TpApp T tT) = free-vars T ++ₛ free-vars -tT' tT
free-vars {TYPE} (TpEq t₁ t₂) = free-vars t₁ ++ₛ free-vars t₂
free-vars {TYPE} (TpHole pi) = empty-stringset
free-vars {TYPE} (TpLam x tk T) = free-vars-tk tk ++ₛ stringset-remove (free-vars T) x
free-vars {TYPE} (TpVar x) = stringset-single x
free-vars {KIND} KdStar = empty-stringset
free-vars {KIND} (KdHole pi) = empty-stringset
free-vars {KIND} (KdAbs x tk k) = free-vars-tk tk ++ₛ stringset-remove (free-vars k) x

free-vars-arg (Arg t) = free-vars t
free-vars-arg (ArgE tT) = free-vars -tT' tT
free-vars-args = foldr (_++ₛ_ ∘ free-vars-arg) empty-stringset
free-vars-case (Case x cas t T) = foldr (λ {(CaseArg e x tk) → flip trie-remove x}) (free-vars t) cas
free-vars-cases = foldr (_++ₛ_ ∘ free-vars-case) empty-stringset

{-# TERMINATING #-}
erase : ∀ {ed} → ⟦ ed ⟧ → ⟦ ed ⟧
erase-cases : cases → cases
erase-case : case → case
erase-args : args → 𝕃 term
erase-params : params → 𝕃 var
erase-tk : tpkd → tpkd
erase-tT : tmtp → tmtp

erase-tk = erase -tk_
erase-tT = erase -tT_

erase {TERM} (App t t') = App (erase t) (erase t')
erase {TERM} (AppE t T) = erase t
erase {TERM} (Beta t t') = erase t'
erase {TERM} (Delta b? T t) = id-term
erase {TERM} (Hole pi) = Hole pi
erase {TERM} (IotaPair t t' x T) = erase t
erase {TERM} (IotaProj t n) = erase t
erase {TERM} (Lam me x tk t) = if me then erase t else Lam ff x nothing (erase t)
erase {TERM} (LetTm me x T? t t') =
  let t'' = erase t' in
  if ~ me && stringset-contains (free-vars t'') x
    then LetTm ff x nothing (erase t) t''
    else t''
erase {TERM} (LetTp x k T t) = erase t
erase {TERM} (Phi tₑ t₁ t₂) = erase t₂
erase {TERM} (Rho t x T t') = erase t'
erase {TERM} (VarSigma t) = erase t
erase {TERM} (Mu v t T t~ ms) = Mu v (erase t) nothing t~ (erase-cases ms)
erase {TERM} (Sigma mt t T t~ ms) = Sigma nothing (erase t) nothing t~ (erase-cases ms)
erase {TERM} (Var x) = Var x
erase {TYPE} (TpAbs me x tk T) = TpAbs me x (erase-tk tk) (erase T)
erase {TYPE} (TpIota x T₁ T₂) = TpIota x (erase T₁) (erase T₂)
erase {TYPE} (TpApp T tT) = TpApp (erase T) (erase -tT tT)
erase {TYPE} (TpEq t₁ t₂) = TpEq (erase t₁) (erase t₂)
erase {TYPE} (TpHole pi) = TpHole pi
erase {TYPE} (TpLam x tk T) = TpLam x (erase-tk tk) (erase T)
erase {TYPE} (TpVar x) = TpVar x
erase {KIND} KdStar = KdStar
erase {KIND} (KdHole pi) = KdHole pi
erase {KIND} (KdAbs x tk k) = KdAbs x (erase-tk tk) (erase k)

erase-case-args : case-args → case-args
erase-case-args (CaseArg ff x _ :: cas) = CaseArg ff x nothing :: erase-case-args cas
erase-case-args (_ :: cas) = erase-case-args cas
erase-case-args [] = []

erase-cases = map erase-case
erase-case (Case x cas t T) = Case x (erase-case-args cas) (erase t) T

erase-args (Arg t :: as) = erase t :: erase-args as
erase-args (_ :: as) = erase-args as
erase-args [] = []

erase-arg-keep : arg → arg
erase-args-keep : args → args
erase-args-keep = map erase-arg-keep
erase-arg-keep (Arg t) = Arg (erase t)
erase-arg-keep (ArgE tT) = ArgE (erase -tT tT)

erase-params (Param ff x (Tkt T) :: ps) = x :: erase-params ps
erase-params (_ :: ps) = erase-params ps
erase-params [] = []

free-vars-erased : ∀ {ed} → ⟦ ed ⟧ → stringset
free-vars-erased = free-vars ∘ erase

is-free-in : ∀ {ed} → var → ⟦ ed ⟧ → 𝔹
is-free-in x t = stringset-contains (free-vars t) x

are-free-in-h : ∀ {X} → trie X → stringset → 𝔹
are-free-in-h xs fxs = list-any (trie-contains fxs) (map fst (trie-mappings xs))

are-free-in : ∀ {X} {ed} → trie X → ⟦ ed ⟧ → 𝔹
are-free-in xs t = are-free-in-h xs (free-vars t)

erase-if : ∀ {ed} → 𝔹 → ⟦ ed ⟧ → ⟦ ed ⟧
erase-if tt = erase
erase-if ff = id

infix 5 `|_|`
`|_|` = erase
