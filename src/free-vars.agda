module free-vars where
open import lib
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

free-vars? = maybe-else empty-stringset free-vars

free-vars {TERM} (App t me t') = free-vars t ++ₛ free-vars t'
free-vars {TERM} (AppTp t T) = free-vars t ++ₛ free-vars T
free-vars {TERM} (Beta t t') = free-vars? t ++ₛ free-vars? t'
free-vars {TERM} (Delta T t) = free-vars T ++ₛ free-vars t
free-vars {TERM} (Hole pi) = empty-stringset
free-vars {TERM} (IotaPair t t' x T) = free-vars t ++ₛ free-vars t' ++ₛ stringset-remove (free-vars T) x
free-vars {TERM} (IotaProj t n) = free-vars t
free-vars {TERM} (Lam me x atk t) = maybe-else empty-stringset free-vars atk ++ₛ stringset-remove (free-vars t) x
free-vars {TERM} (LetTm me x T? t t') = free-vars? T? ++ₛ free-vars t ++ₛ stringset-remove (free-vars t') x
free-vars {TERM} (LetTp x k T t) = free-vars k ++ₛ free-vars T ++ₛ stringset-remove (free-vars t) x
free-vars {TERM} (Open o x t) = stringset-insert (free-vars t) x
free-vars {TERM} (Phi tₑ t₁ t₂) = free-vars tₑ ++ₛ free-vars t₁ ++ₛ free-vars t₂
free-vars {TERM} (Rho t x T t') = free-vars t ++ₛ stringset-remove (free-vars T) x ++ₛ free-vars t'
free-vars {TERM} (Sigma t) = free-vars t
free-vars {TERM} (Mu μ t T ~t cs) = free-vars t ++ₛ free-vars? T ++ₛ free-vars ~t ++ₛ free-vars-cases cs
free-vars {TERM} (Var x) = stringset-single x
free-vars {TYPE} (TpAbs me x atk T) = free-vars atk ++ₛ stringset-remove (free-vars T) x
free-vars {TYPE} (TpIota x T₁ T₂) = free-vars T₁ ++ₛ stringset-remove (free-vars T₂) x
free-vars {TYPE} (TpApp T T') = free-vars T ++ₛ free-vars T'
free-vars {TYPE} (TpAppt T t) = free-vars T ++ₛ free-vars t
free-vars {TYPE} (TpEq t₁ t₂) = free-vars t₁ ++ₛ free-vars t₂
free-vars {TYPE} (TpHole pi) = empty-stringset
free-vars {TYPE} (TpLam x atk T) = free-vars atk ++ₛ stringset-remove (free-vars T) x
free-vars {TYPE} (TpVar x) = stringset-single x
free-vars {KIND} KdStar = empty-stringset
free-vars {KIND} (KdAbs x atk k) = free-vars atk ++ₛ stringset-remove (free-vars k) x
free-vars {TPKD} (Tkt T) = free-vars T
free-vars {TPKD} (Tkk k) = free-vars k

free-vars-arg (TmArg me t) = free-vars t
free-vars-arg (TpArg T) = free-vars T
free-vars-args = foldr (_++ₛ_ ∘ free-vars-arg) empty-stringset
free-vars-case (Case x cas t) = foldr (λ {(CaseArg e x) → flip trie-remove x}) (free-vars t) cas
free-vars-cases = foldr (_++ₛ_ ∘ free-vars-case) empty-stringset

{-# TERMINATING #-}
erase : ∀ {ed} → ⟦ ed ⟧ → ⟦ ed ⟧
erase-cases : cases → cases
erase-case : case → case
erase-args : args → 𝕃 term
erase-params : params → 𝕃 var

erase {TERM} (App t me t') = if me then erase t else App (erase t) ff (erase t')
erase {TERM} (AppTp t T) = erase t
erase {TERM} (Beta t t') = maybe-else id-term erase t'
erase {TERM} (Delta T t) = id-term
erase {TERM} (Hole pi) = Hole pi
erase {TERM} (IotaPair t t' x T) = erase t
erase {TERM} (IotaProj t n) = erase t
erase {TERM} (Lam me x atk t) = if me then erase t else Lam ff x nothing (erase t)
erase {TERM} (LetTm me x T? t t') =
  let t'' = erase t' in
  if ~ me && stringset-contains (free-vars t'') x
    then LetTm ff x nothing (erase t) t''
    else t''
erase {TERM} (LetTp x k T t) = erase t
erase {TERM} (Open o x t) = erase t
erase {TERM} (Phi tₑ t₁ t₂) = erase t₂
erase {TERM} (Rho t x T t') = erase t'
erase {TERM} (Sigma t) = erase t
erase {TERM} (Mu μ t T ~t cs) = Mu (either-else' μ (inj₁ ∘ maybe-map erase) inj₂) (erase t) nothing (erase ~t) (erase-cases cs)
erase {TERM} (Var x) = Var x
erase {TYPE} (TpAbs me x atk T) = TpAbs me x (erase atk) (erase T)
erase {TYPE} (TpIota x T₁ T₂) = TpIota x (erase T₁) (erase T₂)
erase {TYPE} (TpApp T T') = TpApp (erase T) (erase T')
erase {TYPE} (TpAppt T t) = TpAppt (erase T) (erase t)
erase {TYPE} (TpEq t₁ t₂) = TpEq (erase t₁) (erase t₂)
erase {TYPE} (TpHole pi) = TpHole pi
erase {TYPE} (TpLam x atk T) = TpLam x (erase atk) (erase T)
erase {TYPE} (TpVar x) = TpVar x
erase {KIND} KdStar = KdStar
erase {KIND} (KdAbs x atk k) = KdAbs x (erase atk) (erase k)
erase {TPKD} (Tkt T) = Tkt (erase T)
erase {TPKD} (Tkk k) = Tkk (erase k)

erase-case-args : case-args → case-args
erase-case-args (CaseArg CaseArgTm x :: cas) = CaseArg CaseArgTm x :: erase-case-args cas
erase-case-args (_ :: cas) = erase-case-args cas
erase-case-args [] = []

erase-cases = map erase-case
erase-case (Case x cas t) = Case x (erase-case-args cas) (erase t)

erase-args (TmArg ff t :: as) = erase t :: erase-args as
erase-args (_ :: as) = erase-args as
erase-args [] = []

erase-params (Param ff x (Tkt T) :: ps) = x :: erase-params ps
erase-params (_ :: ps) = erase-params ps
erase-params [] = []

free-vars-erased : ∀ {ed} → ⟦ ed ⟧ → stringset
free-vars-erased = free-vars ∘ erase

is-free-in : ∀ {ed} → var → ⟦ ed ⟧ → 𝔹
is-free-in x t = stringset-contains (free-vars t) x

erase-if : ∀ {ed} → 𝔹 → ⟦ ed ⟧ → ⟦ ed ⟧
erase-if tt = erase
erase-if ff = id
