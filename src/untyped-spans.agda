import cedille-options
open import general-util

module untyped-spans (options : cedille-options.options) {F : Set → Set} {{monadF : monad F}} where

open import lib
open import ctxt
open import cedille-types
open import spans options {F}
open import syntax-util
open import to-string options


untyped-term-spans : term → spanM ⊤
untyped-type-spans : type → spanM ⊤
untyped-kind-spans : kind → spanM ⊤
untyped-tk-spans : tk → spanM ⊤
untyped-liftingType-spans : liftingType → spanM ⊤
untyped-optTerm-spans : optTerm → spanM (posinfo → posinfo)
untyped-maybeAtype-spans : maybeAtype → spanM ⊤
untyped-optGuide-spans : optGuide → spanM ⊤
untyped-lterms-spans : lterms → spanM ⊤
untyped-optClass-spans : optClass → spanM ⊤
untyped-defTermOrType-spans : defTermOrType → spanM (spanM ⊤ → spanM ⊤)
untyped-var-spans : posinfo → var → (ctxt → posinfo → var → checking-mode → 𝕃 tagged-val → err-m → span) → spanM ⊤ → spanM ⊤

untyped-var-spans pi x f m = get-ctxt λ Γ → with-ctxt (ctxt-var-decl pi x Γ) (get-ctxt λ Γ → spanM-add (f Γ pi x untyped [] nothing) ≫span m)

untyped-term-spans (App t me t') = untyped-term-spans t ≫span untyped-term-spans t' ≫span spanM-add (App-span t t' untyped [] nothing)
untyped-term-spans (AppTp t T) = untyped-term-spans t ≫span untyped-type-spans T ≫span spanM-add (AppTp-span t T untyped [] nothing)
untyped-term-spans (Beta pi ot ot') = untyped-optTerm-spans ot ≫=span λ f → untyped-optTerm-spans ot' ≫=span λ f' → spanM-add (Beta-span pi (f' (f (posinfo-plus pi 1))) untyped [] nothing)
untyped-term-spans (Chi pi mT t) = untyped-maybeAtype-spans mT ≫span untyped-term-spans t ≫span get-ctxt λ Γ → spanM-add (Chi-span Γ pi mT t untyped [] nothing)
untyped-term-spans (Delta pi mT t) = untyped-maybeAtype-spans mT ≫span untyped-term-spans t ≫span get-ctxt λ Γ → spanM-add (Delta-span Γ pi mT t untyped [] nothing)
untyped-term-spans (Epsilon pi lr mm t) = untyped-term-spans t ≫span spanM-add (Epsilon-span pi lr mm t untyped [] nothing)
untyped-term-spans (Hole pi) = get-ctxt λ Γ → spanM-add (hole-span Γ pi nothing [])
untyped-term-spans (IotaPair pi t t' og pi') = untyped-term-spans t ≫span untyped-term-spans t' ≫span untyped-optGuide-spans og ≫span spanM-add (IotaPair-span pi pi' untyped [] nothing)
untyped-term-spans (IotaProj t n pi) = untyped-term-spans t ≫span spanM-add (IotaProj-span t pi untyped [] nothing)
untyped-term-spans (Lam pi l pi' x oc t) = untyped-optClass-spans oc ≫span get-ctxt λ Γ → spanM-add (Lam-span Γ untyped pi l x oc t [] nothing) ≫span untyped-var-spans pi' x Var-span (untyped-term-spans t)
untyped-term-spans (Let pi d t) = untyped-defTermOrType-spans d ≫=span λ f → f (untyped-term-spans t) ≫span get-ctxt λ Γ → spanM-add (Let-span Γ untyped pi d t [] nothing)
untyped-term-spans (Parens pi t pi') = untyped-term-spans t
untyped-term-spans (Phi pi t t' t'' pi') = untyped-term-spans t ≫span untyped-term-spans t' ≫span untyped-term-spans t'' ≫span spanM-add (Phi-span pi pi' untyped [] nothing)
untyped-term-spans (Rho pi op on t og t') = untyped-term-spans t ≫span untyped-term-spans t' ≫span spanM-add (mk-span "Rho" pi (term-end-pos t') (ll-data-term :: [ checking-data untyped ]) nothing)
untyped-term-spans (Sigma pi t) = untyped-term-spans t ≫span get-ctxt λ Γ → spanM-add (mk-span "Sigma" pi (term-end-pos t) (ll-data-term :: [ checking-data untyped ]) nothing)
untyped-term-spans (Theta pi θ t ls) = untyped-term-spans t ≫span untyped-lterms-spans ls ≫span get-ctxt λ Γ → spanM-add (Theta-span Γ pi θ t ls untyped [] nothing)
untyped-term-spans (Var pi x) = get-ctxt λ Γ →
  spanM-add (Var-span Γ pi x untyped [] (if ctxt-binds-var Γ x then nothing else just "This variable is not currently in scope."))

untyped-type-spans (Abs pi b pi' x atk T) = untyped-tk-spans atk ≫span spanM-add (TpQuant-span (binder-is-pi b) pi x atk T untyped [] nothing) ≫span untyped-var-spans pi' x (if tk-is-type atk then Var-span else TpVar-span) (untyped-type-spans T)
untyped-type-spans (Iota pi pi' x T T') = untyped-type-spans T ≫span spanM-add (Iota-span pi T' untyped [] nothing) ≫span untyped-var-spans pi' x TpVar-span (untyped-type-spans T')
untyped-type-spans (Lft pi pi' x t lT) = untyped-liftingType-spans lT ≫span spanM-add (Lft-span pi x t untyped [] nothing) ≫span untyped-var-spans pi' x Var-span (untyped-term-spans t)
untyped-type-spans (NoSpans T pi) = spanMok
untyped-type-spans (TpApp T T') = untyped-type-spans T ≫span untyped-type-spans T' ≫span spanM-add (TpApp-span T T' untyped [] nothing)
untyped-type-spans (TpAppt T t) = untyped-type-spans T ≫span untyped-term-spans t ≫span spanM-add (TpAppt-span T t untyped [] nothing)
untyped-type-spans (TpArrow T a T') = untyped-type-spans T ≫span untyped-type-spans T' ≫span spanM-add (TpArrow-span T T' untyped [] nothing)
untyped-type-spans (TpEq pi t t' pi') = untyped-term-spans t ≫span untyped-term-spans t' ≫span spanM-add (TpEq-span pi t t' pi' untyped [] nothing)
untyped-type-spans (TpHole pi) = get-ctxt λ Γ → spanM-add (tp-hole-span Γ pi nothing [])
untyped-type-spans (TpLambda pi pi' x atk T) = untyped-tk-spans atk ≫span spanM-add (TpLambda-span pi pi' atk T untyped [] nothing) ≫span untyped-var-spans pi' x TpVar-span (untyped-type-spans T)
untyped-type-spans (TpParens pi T pi') = untyped-type-spans T
untyped-type-spans (TpVar pi x) = get-ctxt λ Γ →
  spanM-add (TpVar-span Γ pi x untyped [] (if ctxt-binds-var Γ x then nothing else just "This variable is not currently in scope."))

untyped-kind-spans (KndArrow k k') = untyped-kind-spans k ≫span untyped-kind-spans k' ≫span spanM-add (KndArrow-span k k' untyped nothing)
untyped-kind-spans (KndParens pi k pi') = untyped-kind-spans k
untyped-kind-spans (KndPi pi pi' x atk k) = untyped-tk-spans atk ≫span spanM-add (KndPi-span pi x atk k untyped nothing) ≫span untyped-var-spans pi' x (if tk-is-type atk then Var-span else TpVar-span) (untyped-kind-spans k)
untyped-kind-spans (KndTpArrow T k) = untyped-type-spans T ≫span untyped-kind-spans k ≫span spanM-add (KndTpArrow-span T k untyped nothing)
untyped-kind-spans (KndVar pi x as) = get-ctxt λ Γ →
  spanM-add (KndVar-span Γ (pi , x) (kvar-end-pos pi x as) ParamsNil untyped [] (if ctxt-binds-var Γ x then nothing else just "This variable is not currently in scope."))
untyped-kind-spans (Star pi) = spanM-add (Star-span pi untyped nothing)

untyped-liftingType-spans lT = spanMok -- Unimplemented

untyped-tk-spans (Tkt T) = untyped-type-spans T
untyped-tk-spans (Tkk k) = untyped-kind-spans k

untyped-optTerm-spans NoTerm = spanMr λ pi → pi
untyped-optTerm-spans (SomeTerm t pi) = untyped-term-spans t ≫span spanMr λ _ → pi

untyped-maybeAtype-spans NoAtype = spanMok
untyped-maybeAtype-spans (Atype T) = untyped-type-spans T

untyped-optGuide-spans NoGuide = spanMok
untyped-optGuide-spans (Guide pi x T) = untyped-var-spans pi x Var-span (untyped-type-spans T)

untyped-lterms-spans (LtermsNil pi) = spanMok
untyped-lterms-spans (LtermsCons me t ls) = untyped-term-spans t ≫span untyped-lterms-spans ls

untyped-optClass-spans NoClass = spanMok
untyped-optClass-spans (SomeClass atk) = untyped-tk-spans atk

untyped-defTermOrType-spans (DefTerm pi x NoCheckType t) = untyped-term-spans t ≫span get-ctxt λ Γ → with-ctxt (ctxt-var-decl pi x Γ) (spanMr λ x → x)
untyped-defTermOrType-spans (DefTerm pi x (Type T) t) = untyped-term-spans t ≫span untyped-type-spans T ≫span get-ctxt λ Γ → with-ctxt (ctxt-var-decl pi x Γ) (spanMr λ x → x)
untyped-defTermOrType-spans (DefType pi x k T) = untyped-kind-spans k ≫span untyped-type-spans T ≫span get-ctxt λ Γ → with-ctxt (ctxt-var-decl pi x Γ) (spanMr λ x → x)
