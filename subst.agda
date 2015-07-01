module subst where

open import lib
open import cedille-types
open import rename
open import tpstate

-- the 𝔹 tells whether or not we replaced the variable (as otherwise this could be a little bit of a nuisance to check)
term-var-subst : Set
term-var-subst = renamectxt → var → term × 𝔹

type-var-subst : Set
type-var-subst = renamectxt → var → type × 𝔹

var-substs : Set
var-substs = term-var-subst × type-var-subst

-- the given predicate should tell us which names to avoid renaming to (these should be free variables and defined symbols)
subst-ctorseth : renamectxt → (var → 𝔹) → var-substs → ctorset → ctorset
subst-liftingTypeh : renamectxt → (var → 𝔹) → var-substs → liftingType → liftingType
subst-typeh : renamectxt → (var → 𝔹) → var-substs → type → type
subst-kindh : renamectxt → (var → 𝔹) → var-substs → kind → kind
subst-tkh : renamectxt → (var → 𝔹) → var-substs → tk → tk
subst-termh : renamectxt → (var → 𝔹) → var-substs → term → term

subst-termh r b σ (Lam y t') = 
  let y' = rename-away-from y b r in
    Lam y' (subst-termh (renamectxt-insert r y y') b σ t')
subst-termh r b σ (App t1 t2) = App (subst-termh r b σ t1) (subst-termh r b σ t2)
subst-termh r b σ (Parens t') = subst-termh r b σ t'
subst-termh r b (σtrm , σtp) (Var y) = fst (σtrm r y)

subst-ctorseth r b σ (Add trm tp' Θ) = Add trm (subst-typeh r b σ tp') (subst-ctorseth r b σ Θ)
subst-ctorseth r b σ Empty = Empty

private 
  unimplemented : type
  unimplemented = U

subst-typeh r b σ (AbsTp1 o x tp1 tp2) = 
  let x' = rename-away-from x b r in
     AbsTp1 o x' (subst-typeh r b σ tp1) (subst-typeh (renamectxt-insert r x x') b σ tp2)

subst-typeh r b σ (AbsTp2 o x a tp') = 
  let x' = rename-away-from x b r in
    AbsTp2 o x' (subst-tkh r b σ a) (subst-typeh (renamectxt-insert r x x') b σ tp')

subst-typeh r b σ (Lft trm tp) = 
    Lft (subst-termh r b σ trm) (subst-liftingTypeh r b σ tp)

subst-typeh r b σ (Nu x k Θ tp) = 
  let x' = rename-away-from x b r in
  let r' = renamectxt-insert r x x' in
    Nu x' (subst-kindh r b σ k) (subst-ctorseth r' b σ Θ) (subst-typeh r' b σ tp)
  
subst-typeh r b σ (TpApp tp1 tp2) = TpApp (subst-typeh r b σ tp1) (subst-typeh r b σ tp2)
subst-typeh r b σ (TpAppt tp' t) = TpAppt (subst-typeh r b σ tp') (subst-termh r b σ t)
subst-typeh r b σ (TpArrow tp1 tp2) = TpArrow (subst-typeh r b σ tp1) (subst-typeh r b σ tp2)
subst-typeh r b σ (TpParens tp') = subst-typeh r b σ tp'
subst-typeh r b (σtrm , σtp) (TpVar x) = fst (σtp r x)
subst-typeh r b σ U = U

subst-liftingTypeh r b (σtrm , σtp) LiftStar = LiftStar
subst-liftingTypeh r b σ (LiftPi x tp ltp) = 
  let x' = rename-away-from x b r in
    LiftPi x' (subst-typeh r b σ tp) (subst-liftingTypeh (renamectxt-insert r x x') b σ ltp)
subst-liftingTypeh r b σ (LiftArrow ltp1 ltp2) = 
  LiftArrow (subst-liftingTypeh r b σ ltp1) (subst-liftingTypeh r b σ ltp2)
subst-liftingTypeh r b σ (LiftTpArrow t l) = 
  LiftTpArrow (subst-typeh r b σ t) (subst-liftingTypeh r b σ l)
subst-liftingTypeh r b σ (LiftParens ltp) = subst-liftingTypeh r b σ ltp

subst-tkh r b σ (Tkk k) = Tkk (subst-kindh r b σ k)
subst-tkh r b σ (Tkt t) = Tkt (subst-typeh r b σ t)

subst-kindh r b σ (KndParens k) = subst-kindh r b σ k 
subst-kindh r b σ (KndArrow k1 k2) = KndArrow (subst-kindh r b σ k1) (subst-kindh r b σ k2)
subst-kindh r b σ (KndTpArrow t k) = KndTpArrow (subst-typeh r b σ t) (subst-kindh r b σ k)
subst-kindh r b σ (KndPi x a k) = 
  let x' = rename-away-from x b r in
    KndPi x' (subst-tkh r b σ a) (subst-kindh (renamectxt-insert r x x') b σ k)
subst-kindh r b σ (KndVar x) = KndVar x
subst-kindh r b σ Star = Star

-- the first var is the one for which we are substituting, which we assume needs no renaming
eq-subst-var : renamectxt → var → var → 𝔹
eq-subst-var r v x = v =string (renamectxt-rep r x)

type-var-do-subst : type → var → type-var-subst
type-var-do-subst tp v r x = if eq-subst-var r v x then (tp , tt) else (TpVar (renamectxt-rep r x) , ff)

type-var-no-subst : type-var-subst
type-var-no-subst r x = TpVar (renamectxt-rep r x) , ff

term-var-do-subst : term → var → term-var-subst
term-var-do-subst trm v r x = if eq-subst-var r v x then (trm , tt) else (Var (renamectxt-rep r x) , ff)

term-var-no-subst : term-var-subst
term-var-no-subst r x = Var (renamectxt-rep r x) , ff

type-var-substs : type → var → var-substs
type-var-substs tp v = term-var-no-subst , type-var-do-subst tp v

term-var-substs : term → var → var-substs
term-var-substs trm v = term-var-do-subst trm v , type-var-no-subst

subst-add-var-to-avoid : (var → 𝔹) → var → (var → 𝔹)
subst-add-var-to-avoid b v x = (x =string v) || b x

type-subst-ctorset : renamectxt → (var → 𝔹) → type → var → ctorset → ctorset
type-subst-ctorset r b tp v Θ = subst-ctorseth r (subst-add-var-to-avoid b v) (type-var-substs tp v) Θ 

type-subst-type : renamectxt → (var → 𝔹) → type → var → type → type
type-subst-type r b tp v tp' = subst-typeh r (subst-add-var-to-avoid b v) (type-var-substs tp v) tp'

term-subst-term : renamectxt → (var → 𝔹) → term → var → term → term
term-subst-term r b trm v trm' = subst-termh r (subst-add-var-to-avoid b v) (term-var-substs trm v) trm'

term-subst-type : renamectxt → (var → 𝔹) → term → var → type → type
term-subst-type r b trm v trm' = subst-typeh r (subst-add-var-to-avoid b v) (term-var-substs trm v) trm'

term-subst-kind : renamectxt → (var → 𝔹) → term → var → kind → kind
term-subst-kind r b trm v trm' = subst-kindh r (subst-add-var-to-avoid b v) (term-var-substs trm v) trm'

type-subst-kind : renamectxt → (var → 𝔹) → type → var → kind → kind
type-subst-kind r b trm v trm' = subst-kindh r (subst-add-var-to-avoid b v) (type-var-substs trm v) trm'

term-subst-liftingType : renamectxt → (var → 𝔹) → term → var → liftingType → liftingType
term-subst-liftingType r b trm v trm' = subst-liftingTypeh r (subst-add-var-to-avoid b v) (term-var-substs trm v) trm'

rename-term : renamectxt → (var → 𝔹) → term → term
rename-term r b t = subst-termh r b (term-var-no-subst , type-var-no-subst) t

rename-type : renamectxt → (var → 𝔹) → type → type
rename-type r b t = subst-typeh r b (term-var-no-subst , type-var-no-subst) t

