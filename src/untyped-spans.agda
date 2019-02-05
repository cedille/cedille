import cedille-options
open import general-util

module untyped-spans (options : cedille-options.options) {F : Set → Set} {{monadF : monad F}} where

open import lib
open import ctxt
open import cedille-types
open import conversion
open import spans options {F}
open import syntax-util
open import to-string options
open import is-free

{-# TERMINATING #-}
untyped-term-spans : term → spanM ⊤
untyped-type-spans : type → spanM ⊤
untyped-kind-spans : kind → spanM ⊤
untyped-tk-spans : tk → spanM ⊤
untyped-liftingType-spans : liftingType → spanM ⊤
untyped-optTerm-spans : optTerm → spanM (posinfo → posinfo)
untyped-optType-spans : optType → spanM ⊤
untyped-optGuide-spans : optGuide → spanM (𝕃 tagged-val)
untyped-lterms-spans : lterms → spanM ⊤
untyped-optClass-spans : optClass → spanM ⊤
untyped-defTermOrType-spans : posinfo → (ctxt → posinfo → var → (atk : tk) → (if tk-is-type atk then term else type) → span) → defTermOrType → spanM ⊤ → spanM ⊤
untyped-var-spans : posinfo → var → (ctxt → posinfo → var → checking-mode → 𝕃 tagged-val → err-m → span) → spanM ⊤ → spanM ⊤
untyped-caseArgs-spans : caseArgs → (body : term) → spanM (𝕃 tagged-val)
untyped-case-spans : case → (ℕ → ℕ → err-m) → spanM ((ℕ → ℕ → err-m) × 𝕃 tagged-val)
untyped-cases-spans : cases → spanM (err-m × 𝕃 tagged-val)

untyped-var-spans pi x f m = get-ctxt λ Γ → with-ctxt (ctxt-var-decl-loc pi x Γ) (get-ctxt λ Γ → spanM-add (f Γ pi x untyped [] nothing) ≫span m)

untyped-term-spans (App t me t') = untyped-term-spans t ≫span untyped-term-spans t' ≫span spanM-add (App-span ff t t' untyped [] nothing)
untyped-term-spans (AppTp t T) = untyped-term-spans t ≫span untyped-type-spans T ≫span spanM-add (AppTp-span t T untyped [] nothing)
untyped-term-spans (Beta pi ot ot') = untyped-optTerm-spans ot ≫=span λ f → untyped-optTerm-spans ot' ≫=span λ f' → spanM-add (Beta-span pi (f' (f (posinfo-plus pi 1))) untyped [] nothing)
untyped-term-spans (Chi pi mT t) = untyped-optType-spans mT ≫span untyped-term-spans t ≫span get-ctxt λ Γ → spanM-add (Chi-span Γ pi mT t untyped [] nothing)
untyped-term-spans (Delta pi mT t) = untyped-optType-spans mT ≫span untyped-term-spans t ≫span get-ctxt λ Γ → spanM-add (Delta-span Γ pi mT t untyped [] nothing)
untyped-term-spans (Epsilon pi lr mm t) = untyped-term-spans t ≫span spanM-add (Epsilon-span pi lr mm t untyped [] nothing)
untyped-term-spans (Hole pi) = get-ctxt λ Γ → spanM-add (hole-span Γ pi nothing [])
untyped-term-spans (IotaPair pi t t' og pi') = untyped-term-spans t ≫span untyped-term-spans t' ≫span untyped-optGuide-spans og ≫=span λ tvs → spanM-add (IotaPair-span pi pi' untyped tvs nothing)
untyped-term-spans (IotaProj t n pi) = untyped-term-spans t ≫span spanM-add (IotaProj-span t pi untyped [] nothing)
untyped-term-spans (Lam pi me pi' x oc t) =
  untyped-optClass-spans oc
  ≫span get-ctxt λ Γ → spanM-add (Lam-span Γ untyped pi pi' me x (Tkt $ TpHole pi) t [] occursCheck)
  ≫span untyped-var-spans pi' x Var-span (untyped-term-spans t)
  where
  occursCheck = maybe-if (me && is-free-in skip-erased x t) ≫maybe just "The bound variable occurs free in the erasure of the body (not allowed)"
untyped-term-spans (Let pi fe d t) =
  untyped-defTermOrType-spans pi (λ Γ pi' x atk val → Let-span Γ untyped pi pi' fe x atk val t [] nothing) d (untyped-term-spans t)
  -- ≫span get-ctxt λ Γ → spanM-add (Let-span Γ untyped pi d t [] nothing)
untyped-term-spans (Open pi o pi' x t) = get-ctxt λ Γ → spanM-add (Open-span Γ o pi' x t untyped [] nothing) ≫span spanM-add (Var-span Γ pi' x untyped [] (maybe-not (ctxt-lookup-term-loc Γ x) ≫maybe just "This term variable is not currently in scope")) ≫span untyped-term-spans t
untyped-term-spans (Parens pi t pi') = untyped-term-spans t
untyped-term-spans (Phi pi t t' t'' pi') = untyped-term-spans t ≫span untyped-term-spans t' ≫span untyped-term-spans t'' ≫span spanM-add (Phi-span pi pi' untyped [] nothing)
untyped-term-spans (Rho pi op on t og t') = untyped-term-spans t ≫span untyped-term-spans t' ≫span untyped-optGuide-spans og ≫=span λ tvs → spanM-add (mk-span "Rho" pi (term-end-pos t') (ll-data-term :: checking-data untyped :: tvs) nothing)
untyped-term-spans (Sigma pi t) = untyped-term-spans t ≫span get-ctxt λ Γ → spanM-add (mk-span "Sigma" pi (term-end-pos t) (ll-data-term :: [ checking-data untyped ]) nothing)
untyped-term-spans (Theta pi θ t ls) = untyped-term-spans t ≫span untyped-lterms-spans ls ≫span get-ctxt λ Γ → spanM-add (Theta-span Γ pi θ t ls untyped [] nothing)
untyped-term-spans (Var pi x) = get-ctxt λ Γ →
  spanM-add (Var-span Γ pi x untyped [] (if ctxt-binds-var Γ x then nothing else just "This variable is not currently in scope."))
untyped-term-spans (Mu pi pi' x t ot pi'' cs pi''') = get-ctxt λ Γ → untyped-term-spans t ≫span with-ctxt (ctxt-var-decl x Γ) (get-ctxt λ Γ → spanM-add (Var-span Γ pi' x untyped [ binder-data (ctxt-var-decl-loc pi' x Γ) pi' x (Tkt (TpHole pi')) NotErased nothing pi'' pi''' ] nothing) ≫span untyped-cases-spans cs) ≫=span uncurry λ e ts → spanM-add (Mu-span Γ pi (just x) pi''' (optType-elim ot nothing just) untyped ts e)
untyped-term-spans (Mu' pi ot t oT pi' cs pi'') = get-ctxt λ Γ → untyped-optTerm-spans ot ≫span untyped-term-spans t ≫span untyped-optType-spans oT ≫span untyped-cases-spans cs ≫=span uncurry λ e ts → spanM-add (Mu-span Γ pi nothing pi'' (optType-elim oT nothing just) untyped ts e)


untyped-caseArgs-spans [] t = untyped-term-spans t ≫span spanMr []
untyped-caseArgs-spans (c :: cs) t with caseArg-to-var c
...| pi , x , me , ll =
  let e? = maybe-if (me && is-free-in skip-erased x (caseArgs-to-lams cs t)) ≫maybe
            just "The bound variable occurs free in the erasure of the body (not allowed)"
      f = if ll then Var-span else TpVar-span in
  get-ctxt λ Γ →
  spanM-add (f (ctxt-var-decl-loc pi x Γ) pi x untyped [] e?) ≫span
  with-ctxt (ctxt-var-decl x Γ) (untyped-caseArgs-spans cs t) ≫=span λ ts →
  spanMr (binder-data (ctxt-var-decl x Γ) pi x (if ll then Tkt (TpHole pi) else Tkk star) me nothing (term-start-pos t) (term-end-pos t) :: ts)

untyped-case-spans (Case pi x cas t) fₑ =
  get-ctxt λ Γ →
  let m = untyped-caseArgs-spans cas t
      x' = unqual-all (ctxt-get-qualif Γ) $ unqual-local x
      eᵤ = just $ "This is not a valid constructor name"
      eₗ = just $ "Constructor's datatype has a different number of constructors than " ^ x'
      eᵢ = just $ "This constructor overlaps with " ^ x' in
  case qual-lookup Γ x of λ where
    (just (as , ctr-def ps? T Cₗ cᵢ cₐ , _ , _)) →
      spanM-add (Var-span Γ pi x untyped [] $ fₑ Cₗ cᵢ) ≫span m ≫=span λ s →
      spanMr ((λ Cₗ' cᵢ' → if Cₗ =ℕ Cₗ' then if cᵢ =ℕ cᵢ' then eᵢ else nothing else eₗ) , s)
    _ →
      spanM-add (Var-span Γ pi x untyped [] eᵤ) ≫span m ≫=span λ s →
      spanMr ((λ _ _ → nothing) , s)

untyped-cases-spans ms =
  let eₗ = just $ "Constructor's datatype should have " ^ ℕ-to-string (length ms) ^
             " constructor" ^ (if 1 =ℕ length ms then "" else "s") in
  (λ c → foldr c (λ _ → spanMr (nothing , [])) ms λ Cₗ cᵢ → if Cₗ =ℕ length ms then nothing else eₗ)
  λ c m fₑ → untyped-case-spans c fₑ ≫=span uncurry λ e s →
               m e ≫=span (spanMr ∘ map-snd (s ++_))

untyped-type-spans (Abs pi me pi' x atk T) = untyped-tk-spans atk ≫span untyped-var-spans pi' x (if tk-is-type atk then Var-span else TpVar-span) (get-ctxt λ Γ → spanM-add (TpQuant-span Γ (~ me) pi pi' x atk T untyped [] nothing) ≫span untyped-type-spans T)
untyped-type-spans (Iota pi pi' x T T') = untyped-type-spans T ≫span untyped-var-spans pi' x TpVar-span (get-ctxt λ Γ → spanM-add (Iota-span Γ pi pi' x T' untyped [] nothing) ≫span untyped-type-spans T')
untyped-type-spans (Lft pi pi' x t lT) = untyped-liftingType-spans lT ≫span untyped-var-spans pi' x Var-span (get-ctxt λ Γ → spanM-add (Lft-span Γ pi pi' x t untyped [] nothing) ≫span untyped-term-spans t)
untyped-type-spans (NoSpans T pi) = spanMok
untyped-type-spans (TpApp T T') = untyped-type-spans T ≫span untyped-type-spans T' ≫span spanM-add (TpApp-span T T' untyped [] nothing)
untyped-type-spans (TpAppt T t) = untyped-type-spans T ≫span untyped-term-spans t ≫span spanM-add (TpAppt-span T t untyped [] nothing)
untyped-type-spans (TpArrow T a T') = untyped-type-spans T ≫span untyped-type-spans T' ≫span spanM-add (TpArrow-span T T' untyped [] nothing)
untyped-type-spans (TpEq pi t t' pi') = untyped-term-spans t ≫span untyped-term-spans t' ≫span spanM-add (TpEq-span pi t t' pi' untyped [] nothing)
untyped-type-spans (TpHole pi) = get-ctxt λ Γ → spanM-add (tp-hole-span Γ pi nothing [])
untyped-type-spans (TpLambda pi pi' x atk T) = untyped-tk-spans atk ≫span untyped-var-spans pi' x TpVar-span (get-ctxt λ Γ → spanM-add (TpLambda-span Γ pi pi' x atk T untyped [] nothing) ≫span untyped-type-spans T)
untyped-type-spans (TpParens pi T pi') = untyped-type-spans T
untyped-type-spans (TpVar pi x) = get-ctxt λ Γ →
  spanM-add (TpVar-span Γ pi x untyped [] (if ctxt-binds-var Γ x then nothing else just "This variable is not currently in scope."))
untyped-type-spans (TpLet pi d T) =
 untyped-defTermOrType-spans pi (λ Γ pi' x atk val → TpLet-span Γ untyped pi pi' x atk val T [] nothing) d (untyped-type-spans T)
 --≫span get-ctxt λ Γ → spanM-add (TpLet-span Γ untyped pi d T [] nothing)

untyped-kind-spans (KndArrow k k') = untyped-kind-spans k ≫span untyped-kind-spans k' ≫span spanM-add (KndArrow-span k k' untyped nothing)
untyped-kind-spans (KndParens pi k pi') = untyped-kind-spans k
untyped-kind-spans (KndPi pi pi' x atk k) = untyped-tk-spans atk ≫span untyped-var-spans pi' x (if tk-is-type atk then Var-span else TpVar-span) (get-ctxt λ Γ → spanM-add (KndPi-span Γ pi pi' x atk k untyped nothing) ≫span untyped-kind-spans k)
untyped-kind-spans (KndTpArrow T k) = untyped-type-spans T ≫span untyped-kind-spans k ≫span spanM-add (KndTpArrow-span T k untyped nothing)
untyped-kind-spans (KndVar pi x as) = get-ctxt λ Γ →
  spanM-add (KndVar-span Γ (pi , x) (kvar-end-pos pi x as) [] untyped [] (if ctxt-binds-var Γ x then nothing else just "This variable is not currently in scope."))
untyped-kind-spans (Star pi) = spanM-add (Star-span pi untyped nothing)

untyped-liftingType-spans lT = spanMok -- Unimplemented

untyped-tk-spans (Tkt T) = untyped-type-spans T
untyped-tk-spans (Tkk k) = untyped-kind-spans k

untyped-optTerm-spans NoTerm = spanMr λ pi → pi
untyped-optTerm-spans (SomeTerm t pi) = untyped-term-spans t ≫span spanMr λ _ → pi

untyped-optType-spans NoType = spanMok
untyped-optType-spans (SomeType T) = untyped-type-spans T

untyped-optGuide-spans NoGuide = spanMr []
untyped-optGuide-spans (Guide pi x T) = untyped-var-spans pi x Var-span (untyped-type-spans T) ≫span get-ctxt λ Γ → spanMr [ binder-data Γ pi x (Tkt $ TpHole pi) NotErased nothing (type-start-pos T) (type-end-pos T) ]

untyped-lterms-spans [] = spanMok
untyped-lterms-spans ((Lterm me t) :: ls) = untyped-term-spans t ≫span untyped-lterms-spans ls

untyped-optClass-spans NoClass = spanMok
untyped-optClass-spans (SomeClass atk) = untyped-tk-spans atk

untyped-defTermOrType-spans pi s (DefTerm pi' x NoType t) m =
  untyped-term-spans t ≫span
  get-ctxt λ Γ → with-ctxt (ctxt-var-decl-loc pi' x Γ) $
  get-ctxt λ Γ → spanM-add (s Γ pi' x (Tkt $ TpHole pi') t) ≫span
                 spanM-add (Var-span Γ pi' x untyped [] nothing) ≫span m
untyped-defTermOrType-spans pi s (DefTerm pi' x (SomeType tp) t) m =
  untyped-type-spans tp ≫span
  untyped-term-spans t ≫span
  get-ctxt λ Γ → with-ctxt (ctxt-var-decl-loc pi' x Γ) $
  get-ctxt λ Γ → spanM-add (s Γ pi' x (Tkt $ TpHole pi') t) ≫span
                 spanM-add (Var-span Γ pi' x untyped [] nothing) ≫span m
untyped-defTermOrType-spans pi s (DefType pi' x k tp) m =
  untyped-kind-spans k ≫span
  untyped-type-spans tp ≫span
  get-ctxt λ Γ → with-ctxt (ctxt-var-decl-loc pi' x Γ) $
  get-ctxt λ Γ → spanM-add (s Γ pi' x (Tkk k) tp) ≫span
                 spanM-add (TpVar-span Γ pi' x untyped [] nothing) ≫span m
