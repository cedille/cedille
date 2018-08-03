module ctxt where

open import lib
open import cedille-types
open import ctxt-types public
open import subst
open import general-util
open import syntax-util

new-sym-info-trie : trie sym-info
new-sym-info-trie = trie-insert empty-trie compileFail-qual ((term-decl compileFailType) , "missing" , "missing")

new-qualif : qualif
new-qualif = trie-insert empty-trie compileFail (compileFail-qual , ArgsNil)

qualif-nonempty : qualif → 𝔹
qualif-nonempty q = trie-nonempty (trie-remove q compileFail)

new-ctxt : (filename modname : string) → ctxt
new-ctxt fn mn = mk-ctxt (fn , mn , ParamsNil , new-qualif) (empty-trie , empty-trie , empty-trie , empty-trie , 0 , []) new-sym-info-trie empty-trie

empty-ctxt : ctxt
empty-ctxt = new-ctxt "" ""

ctxt-get-info : var → ctxt → maybe sym-info
ctxt-get-info v (mk-ctxt _ _ i _) = trie-lookup i v

ctxt-set-qualif : ctxt → qualif → ctxt
ctxt-set-qualif (mk-ctxt (f , m , p , q') syms i sym-occurrences) q
  = mk-ctxt (f , m , p , q) syms i sym-occurrences

ctxt-get-qualif : ctxt → qualif
ctxt-get-qualif (mk-ctxt (_ , _ , _ , q) _ _ _) = q

ctxt-get-qi : ctxt → var → maybe qualif-info
ctxt-get-qi Γ = trie-lookup (ctxt-get-qualif Γ)

ctxt-qualif-args-length : ctxt → maybeErased → var → maybe ℕ
ctxt-qualif-args-length Γ me v =
  ctxt-get-qi Γ v ≫=maybe λ qv →
  just (me-args-length me (snd qv))

qi-var-if : maybe qualif-info → var → var
qi-var-if (just (v , _)) _ = v
qi-var-if nothing v = v

ctxt-restore-info : ctxt → var → maybe qualif-info → maybe sym-info → ctxt
ctxt-restore-info (mk-ctxt (fn , mn , ps , q) syms i symb-occs) v qi si =
  mk-ctxt (fn , mn , ps , f qi v q) syms (f si (qi-var-if qi v) (trie-remove i (qi-var-if (trie-lookup q v) v))) symb-occs
  where
    f : ∀{A : Set} → maybe A → string → trie A → trie A
    f (just a) s t = trie-insert t s a
    f nothing s t = trie-remove t s

ctxt-restore-info* : ctxt → 𝕃 (string × maybe qualif-info × maybe sym-info) → ctxt
ctxt-restore-info* Γ [] = Γ
ctxt-restore-info* Γ ((v , qi , m) :: ms) = ctxt-restore-info* (ctxt-restore-info Γ v qi m) ms

def-params : defScope → params → defParams
def-params tt ps = nothing
def-params ff ps = just ps

-- TODO add renamectxt to avoid capture bugs?
inst-type : ctxt → params → args → type → type
inst-type Γ ps as T with mk-inst ps as
...| σ , ps' = abs-expand-type ps' (substs-type Γ σ T)

inst-kind : ctxt → params → args → kind → kind
inst-kind Γ ps as k with mk-inst ps as
...| σ , ps' = abs-expand-kind ps' (substs-kind Γ σ k)

-- TODO substs-params
inst-params : ctxt → params → args → params → params
inst-params Γ ps as qs = qs

qualif-term : ctxt → term → term
qualif-term Γ@(mk-ctxt (_ , _ , _ , σ) _ _ _) = substs-term Γ σ

qualif-type : ctxt → type → type
qualif-type Γ@(mk-ctxt (_ , _ , _ , σ) _ _ _) = substs-type Γ σ

qualif-kind : ctxt → kind → kind
qualif-kind Γ@(mk-ctxt (_ , _ , _ , σ) _ _ _) = substs-kind Γ σ

qualif-liftingType : ctxt → liftingType → liftingType
qualif-liftingType Γ@(mk-ctxt (_ , _ , _ , σ) _ _ _) = substs-liftingType Γ σ

qualif-tk : ctxt → tk → tk
qualif-tk Γ (Tkt t) = Tkt (qualif-type Γ t)
qualif-tk Γ (Tkk k) = Tkk (qualif-kind Γ k)

erased-margs : ctxt → stringset
erased-margs Γ = stringset-insert* empty-stringset (erased-params ps)
  where
  ps = ctxt-get-current-params Γ

qualif-params : ctxt → params → params
qualif-params Γ (ParamsCons (Decl pi1 pi1' me x atk pi2) ps) =
  ParamsCons p' (qualif-params Γ ps)
  where p' = Decl pi1 pi1' me (ctxt-get-current-modname Γ # x) (qualif-tk Γ atk) pi2
qualif-params Γ ParamsNil = ParamsNil

qualif-args : ctxt → args → args
qualif-args Γ (ArgsCons (TermArg me t) as) = ArgsCons (TermArg me (qualif-term Γ t)) (qualif-args Γ as)
qualif-args Γ (ArgsCons (TypeArg tp) as) = ArgsCons (TypeArg (qualif-type Γ tp)) (qualif-args Γ as)
qualif-args Γ ArgsNil = ArgsNil

ctxt-term-decl : posinfo → defScope → var → type → ctxt → ctxt
ctxt-term-decl p s v t Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs) =
  mk-ctxt (fn , mn , ps , (qualif-insert-params q v' v ParamsNil))
  syms
  (trie-insert i v' ((term-decl (qualif-type Γ t)) , (fn , p)))
  symb-occs
  where v' = if s iff localScope then p % v else mn # v

ctxt-type-decl : posinfo → defScope → var → kind → ctxt → ctxt
ctxt-type-decl p s v k Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs) =
  mk-ctxt (fn , mn , ps , (qualif-insert-params q v' v ParamsNil))
  syms
  (trie-insert i v' (type-decl (qualif-kind Γ k) , (fn , p)))
  symb-occs
  where v' = if s iff localScope then p % v else mn # v

ctxt-tk-decl : posinfo → defScope → var → tk → ctxt → ctxt
ctxt-tk-decl p s x (Tkt t) Γ = ctxt-term-decl p s x t Γ 
ctxt-tk-decl p s x (Tkk k) Γ = ctxt-type-decl p s x k Γ

-- TODO not sure how this and renaming interacts with module scope
ctxt-var-decl-if : posinfo → var → ctxt → ctxt
ctxt-var-decl-if p v Γ with Γ
... | mk-ctxt (fn , mn , ps , q) syms i symb-occs with trie-lookup i v
... | just (rename-def _ , _) = Γ
... | just (var-decl , _) = Γ
... | _ = mk-ctxt (fn , mn , ps , (trie-insert q v (v , ArgsNil))) syms
  (trie-insert i v (var-decl , (fn , p)))
  symb-occs

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt m syms i _) v with trie-lookup i v 
...                                           | just (rename-def v' , _) = v'
...                                           | _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}

ctxt-rename : posinfo → var → var → ctxt → ctxt
ctxt-rename p v v' Γ @ (mk-ctxt (fn , mn , ps , q) syms i symb-occs) =
  (mk-ctxt (fn , mn , ps , qualif-insert-params q v' v ps) syms
  (trie-insert i v (rename-def v' , (fn , p)))
  symb-occs)

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- lookup mod params from filename
lookup-mod-params : ctxt → var → maybe params
lookup-mod-params (mk-ctxt _ (syms , _ , mn-ps , id) _ _) fn =
  trie-lookup syms fn ≫=maybe λ { (mn , _) →
  trie-lookup mn-ps mn }

-- look for a defined kind for the given var, which is assumed to be a type,
-- then instantiate its parameters
qual-lookup : ctxt → var → maybe (args × sym-info)
qual-lookup Γ@(mk-ctxt (_ , _ , _ , q) _ i _) v =
  trie-lookup q v ≫=maybe λ qv →
  trie-lookup i (fst qv) ≫=maybe λ si →
  just (snd qv , si)

env-lookup : ctxt → var → maybe sym-info
env-lookup Γ@(mk-ctxt (_ , _ , _ , _) _ i _) v =
  trie-lookup i v

-- look for a declared kind for the given var, which is assumed to be a type,
-- otherwise look for a qualified defined kind
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var Γ v with qual-lookup Γ v
... | just (as , type-decl k , _) = just k
... | just (as , type-def (just ps) _ T k , _) = just (inst-kind Γ ps as k)
... | just (as , type-def nothing _ T k , _) = just k
... | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var Γ v with qual-lookup Γ v
... | just (as , term-decl T , _) = just T
... | just (as , term-def (just ps) _ t T , _) = just (inst-type Γ ps as T)
... | just (as , term-def nothing _ t T , _) = just T
... | _ = nothing

ctxt-lookup-tk-var : ctxt → var → maybe tk
ctxt-lookup-tk-var Γ v with qual-lookup Γ v
... | just (as , term-decl T , _) = just (Tkt T)
... | just (as , type-decl k , _) = just (Tkk k)
... | just (as , term-def (just ps) _ t T , _) = just (Tkt (inst-type Γ ps as T))
... | just (as , type-def (just ps) _ T k , _) = just (Tkk (inst-kind Γ ps as k))
... | just (as , term-def nothing _ t T , _) = just (Tkt T)
... | just (as , type-def nothing _ T k , _) = just (Tkk k)
... | _ = nothing

env-lookup-kind-var-qdef : ctxt → var → args → maybe (params × kind)
env-lookup-kind-var-qdef Γ v as with env-lookup Γ v
... | just (kind-def ps1 ps2 k , _) = just (inst-params Γ ps1 as ps2 , inst-kind Γ ps1 as k)
... | _ = nothing

ctxt-lookup-kind-var-qdef : ctxt → var → maybe (params × kind)
ctxt-lookup-kind-var-qdef Γ@(mk-ctxt (_ , _ , _ , q) _ i _) v with trie-lookup q v
... | just (v' , as) = env-lookup-kind-var-qdef Γ v' as
... | _ = nothing


ctxt-term-if-not-opaque : opacity → term → maybe term
ctxt-term-if-not-opaque OpacOpaque _ = nothing
ctxt-term-if-not-opaque OpacTrans  t = just t

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def Γ v with env-lookup Γ v
... | just (term-def nothing opac t _ , _) = ctxt-term-if-not-opaque opac t
... | just (term-udef nothing opac t , _) = ctxt-term-if-not-opaque opac t
... | just (term-def (just ps) opac t _ , _) = ctxt-term-if-not-opaque opac (lam-expand-term ps t)
... | just (term-udef (just ps) opac t , _) = ctxt-term-if-not-opaque opac (lam-expand-term ps t)
... | _ = nothing

ctxt-type-if-not-opaque : opacity → type → maybe type
ctxt-type-if-not-opaque OpacOpaque _ = nothing
ctxt-type-if-not-opaque OpacTrans  t = just t

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def Γ v with env-lookup Γ v
... | just (type-def nothing opac T _ , _) = ctxt-type-if-not-opaque opac T
... | just (type-def (just ps) opac T _ , _) = ctxt-type-if-not-opaque opac (lam-expand-type ps T)
... | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe (params × kind)
ctxt-lookup-kind-var-def Γ x with env-lookup Γ x
... | just (kind-def ps1 ps2 k , _) = just (append-params ps1 ps2 , k)
... | _ = nothing

ctxt-lookup-occurrences : ctxt → var → 𝕃 (var × posinfo × string)
ctxt-lookup-occurrences (mk-ctxt _ _ _ symb-occs) symbol with trie-lookup symb-occs symbol
... | just l = l
... | nothing = []

----------------------------------------------------------------------

ctxt-var-location : ctxt → var → location
ctxt-var-location (mk-ctxt _ _ i _) x with trie-lookup i x
... | just (_ , l) = l
... | nothing = "missing" , "missing"

ctxt-clarify-type-def : ctxt → var → maybe (sym-info × ctxt)
ctxt-clarify-type-def Γ@(mk-ctxt mod@(_ , _ , _ , q) syms i sym-occurrences) x
  = -- trie-lookup q "cNat"  ≫=maybe λ { (x' , _) →
    trie-lookup i x ≫=maybe λ { (ci , l) →
    clarified x ci l } -- }
  where
    ctxt' : var → ctxt-info → location → ctxt
    ctxt' v ci l = mk-ctxt mod syms (trie-insert i v (ci , l)) sym-occurrences

    clarified : var → ctxt-info → location → maybe (sym-info × ctxt)
    clarified v ci@(term-def ps _ t T) l = just ((ci , l) , (ctxt' v (term-def ps OpacTrans t T) l))
    clarified v ci@(term-udef ps _ t) l = just ((ci , l) , (ctxt' v (term-udef ps OpacTrans t) l))
    clarified v ci@(type-def ps _ T k) l = just ((ci , l) , (ctxt' v (type-def ps OpacTrans T k) l))
    clarified _ _ _ = nothing

-- ctxt-clarify-type-def : ctxt → var → maybe ctxt
-- ctxt-clarify-type-def Γ@(mk-ctxt mod syms i sym-occurrences) x with trie-lookup i x
-- ... | just (ci , l) = clarified ci l
--   where
--     ctxt' : ctxt-info → location → ctxt
--     ctxt' ci l = mk-ctxt mod syms (trie-insert i x (ci , l)) sym-occurrences

--     clarified : ctxt-info → location → maybe ctxt
--     clarified (term-def ps _ t T) l = just (ctxt' (term-def ps OpacTrans t T) l)
--     clarified (term-udef ps _ t) l = just (ctxt' (term-udef ps OpacTrans t) l)
--     clarified (type-def ps _ T k) l = just (ctxt' (type-def ps OpacTrans T k) l)
--     clarified _ _ = nothing

-- ... | nothing = nothing

-- ctxt-clarify-term-def : ctxt → var → maybe (ctxt × sym-info)
-- ctxt-clarify-term-def orig-ctxt@(mk-ctxt mod syms i sym-occurrences) x with trie-lookup i x
-- ... | just (ci , l) = (clarified ci l) ≫=maybe (λ Γ' → just (Γ' , (ci , l)))
--   where
--     ctxt' : ctxt-info → location → ctxt
--     ctxt' ci l = mk-ctxt mod syms (trie-insert i x (ci , l)) sym-occurrences

--     clarified : ctxt-info → location → maybe ctxt
--     clarified (term-def ps _ t T) l = just (ctxt' (term-def ps OpacTrans t T) l)
--     clarified (term-udef ps _ t) l = just (ctxt' (term-udef ps OpacTrans t) l)
--     clarified (type-def _ _ _ _) l = just orig-ctxt 
--     clarified _ _ = nothing

-- ... | nothing = nothing

ctxt-clarify-term-def : ctxt → var → maybe ctxt
ctxt-clarify-term-def orig-ctxt@(mk-ctxt mod syms i sym-occurrences) x with trie-lookup i x
... | just (ci , l) = clarified ci l
  where
    ctxt' : ctxt-info → location → ctxt
    ctxt' ci l = mk-ctxt mod syms (trie-insert i x (ci , l)) sym-occurrences

    clarified : ctxt-info → location → maybe ctxt
    clarified (term-def ps _ t T) l = just (ctxt' (term-def ps OpacTrans t T) l)
    clarified (term-udef ps _ t) l = just (ctxt' (term-udef ps OpacTrans t) l)
    clarified (type-def _ _ _ _) l = just orig-ctxt 
    clarified _ _ = nothing

... | nothing = nothing

ctxt-set-sym-info : ctxt → var → sym-info → ctxt
ctxt-set-sym-info (mk-ctxt mod syms i sym-occurrences) x si =
  mk-ctxt mod syms (trie-insert i x si) sym-occurrences

ctxt-restore-clarified-type-def : ctxt → var → sym-info → ctxt
ctxt-restore-clarified-type-def = ctxt-set-sym-info

-- ctxt-restore-clarified-term-def : ctxt → var → sym-info → ctxt
-- ctxt-restore-clarified-term-def = ctxt-set-sym-info

ctxt-set-current-file : ctxt → string → string → ctxt
ctxt-set-current-file (mk-ctxt _ syms i symb-occs) fn mn = mk-ctxt (fn , mn , ParamsNil , new-qualif) syms i symb-occs

ctxt-set-current-mod : ctxt → mod-info → ctxt
ctxt-set-current-mod (mk-ctxt _ syms i symb-occs) m = mk-ctxt m syms i symb-occs

ctxt-add-current-params : ctxt → ctxt
ctxt-add-current-params Γ@(mk-ctxt m@(fn , mn , ps , _) (syms , mn-fn , mn-ps , ids) i symb-occs) =
  mk-ctxt m (trie-insert syms fn (mn , []) , mn-fn , trie-insert mn-ps mn ps , ids) i symb-occs

ctxt-clear-symbol : ctxt → string → ctxt
ctxt-clear-symbol Γ @ (mk-ctxt (fn , mn , pms , q) (syms , mn-fn) i symb-occs) x =
  mk-ctxt (fn , mn , pms , (trie-remove q x)) (trie-map (λ ss → fst ss , remove _=string_ x (snd ss)) syms , mn-fn) (trie-remove i (qualif-var Γ x)) symb-occs

ctxt-clear-symbols : ctxt → 𝕃 string → ctxt
ctxt-clear-symbols Γ [] = Γ
ctxt-clear-symbols Γ (v :: vs) = ctxt-clear-symbols (ctxt-clear-symbol Γ v) vs

ctxt-clear-symbols-of-file : ctxt → (filename : string) → ctxt
ctxt-clear-symbols-of-file (mk-ctxt f (syms , mn-fn , mn-ps) i symb-occs) fn =
  mk-ctxt f (trie-insert syms fn (fst p , []) , trie-insert mn-fn (fst p) fn , mn-ps)
    (hremove i (fst p) (snd p))
    symb-occs
  where
  p = trie-lookup𝕃2 syms fn
  hremove : ∀ {A : Set} → trie A → var → 𝕃 string → trie A
  hremove i mn [] = i
  hremove i mn (x :: xs) = hremove (trie-remove i (mn # x)) mn xs

ctxt-add-current-id : ctxt → ctxt
ctxt-add-current-id (mk-ctxt mod (syms , mn-fn , mn-ps , fn-ids , id , id-fns) is os) =
  mk-ctxt mod (syms , mn-fn , mn-ps , trie-insert fn-ids (fst mod) (suc id) , suc id , (fst mod) :: id-fns) is os

ctxt-initiate-file : ctxt → (filename modname : string) → ctxt
ctxt-initiate-file Γ fn mn = ctxt-add-current-id (ctxt-set-current-file (ctxt-clear-symbols-of-file Γ fn) fn mn)

unqual : ctxt → var → string
unqual (mk-ctxt (_ , _ , _ , q) _ _ _ ) v =
  if qualif-nonempty q
  then unqual-local (unqual-all q v)
  else v

