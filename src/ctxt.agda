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
new-qualif = trie-insert empty-trie compileFail (compileFail-qual , [])

qualif-nonempty : qualif → 𝔹
qualif-nonempty q = trie-nonempty (trie-remove q compileFail)

new-ctxt : (filename modname : string) → ctxt
new-ctxt fn mn = mk-ctxt (fn , mn , [] , new-qualif) (empty-trie , empty-trie , empty-trie , empty-trie , 0 , []) new-sym-info-trie empty-trie (empty-trie , empty-trie , empty-trie , empty-trie)

empty-ctxt : ctxt
empty-ctxt = new-ctxt "" ""

ctxt-get-info : var → ctxt → maybe sym-info
ctxt-get-info v (mk-ctxt _ _ i _ _) = trie-lookup i v

ctxt-set-qualif : ctxt → qualif → ctxt
ctxt-set-qualif (mk-ctxt (f , m , p , q') syms i sym-occurrences Δ) q
  = mk-ctxt (f , m , p , q) syms i sym-occurrences Δ

ctxt-get-qualif : ctxt → qualif
ctxt-get-qualif (mk-ctxt (_ , _ , _ , q) _ _ _ _) = q

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
ctxt-restore-info (mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ) v qi si =
  mk-ctxt (fn , mn , ps , f qi v q) syms (f si (qi-var-if qi v) (trie-remove i (qi-var-if (trie-lookup q v) v))) symb-occs Δ
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
...| σ , ps' = abs-expand-type (substs-params Γ σ ps') (substs Γ σ T)

inst-kind : ctxt → params → args → kind → kind
inst-kind Γ ps as k with mk-inst ps as
...| σ , ps' = abs-expand-kind (substs-params Γ σ ps') (substs Γ σ k)

inst-ctrs : ctxt → params → args → ctrs → ctrs
inst-ctrs Γ ps as c with mk-inst ps as
...| σ , ps' = flip map c λ where
  (Ctr pi x T) → Ctr pi x (abs-expand-type (substs-params Γ σ ps') (substs Γ σ T))

maybe-inst-type = maybe-else (λ as T → T) ∘ inst-type
maybe-inst-kind = maybe-else (λ as T → T) ∘ inst-kind
maybe-inst-ctrs = maybe-else (λ as c → c) ∘ inst-ctrs


qualif-x : ∀ {ℓ} {X : Set ℓ} → (ctxt → qualif → X) → ctxt → X
qualif-x f Γ = f Γ (ctxt-get-qualif Γ)

qualif-term = qualif-x $ substs {TERM}
qualif-type = qualif-x $ substs {TYPE}
qualif-kind = qualif-x $ substs {KIND}
qualif-liftingType = qualif-x $ substs {LIFTINGTYPE}
qualif-tk = qualif-x $ substs {TK}
qualif-params = qualif-x substs-params
qualif-args = qualif-x substs-args

erased-margs : ctxt → stringset
erased-margs = stringset-insert* empty-stringset ∘ (erased-params ∘ ctxt-get-current-params)

ctxt-term-decl-no-qualif : posinfo → var → type → ctxt → ctxt
ctxt-term-decl-no-qualif p v t Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ) =
  mk-ctxt (fn , mn , ps , (qualif-insert-params q v' v []))
  syms
  (trie-insert i v' ((term-decl t) , loc))
  symb-occs
  Δ
  where v' = p % v
        loc = if p =string "missing" then "missing" , "missing" else fn , p

ctxt-type-decl-no-qualif : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl-no-qualif p v k Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ) =
  mk-ctxt (fn , mn , ps , (qualif-insert-params q v' v []))
  syms
  (trie-insert i v' ((type-decl k) , loc))
  symb-occs
  Δ
  where v' = p % v
        loc = if p =string "missing" then "missing" , "missing" else fn , p

ctxt-term-decl : posinfo → var → type → ctxt → ctxt
ctxt-term-decl p v T Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ) =
  let v' =  p % v in
  mk-ctxt (fn , mn , ps , (qualif-insert-params q v' v []))
  syms
  (trie-insert i v' (term-decl (qualif-type Γ T) , fn , p))
  symb-occs
  Δ

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl p v k Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ) =
  let v' = p % v in
  mk-ctxt (fn , mn , ps , (qualif-insert-params q v' v []))
  syms
  (trie-insert i v' (type-decl (qualif-kind Γ k) , fn , p))
  symb-occs
  Δ

ctxt-tk-decl : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ

-- TODO not sure how this and renaming interacts with module scope
ctxt-var-decl-if : var → ctxt → ctxt
ctxt-var-decl-if v Γ with Γ
... | mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ with trie-lookup i v
... | just (rename-def _ , _) = Γ
... | just (var-decl , _) = Γ
... | _ = mk-ctxt (fn , mn , ps , (trie-insert q v (v , []))) syms
  (trie-insert i v (var-decl , "missing" , "missing")) symb-occs Δ

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt m syms i _ _) v with trie-lookup i v 
...                                           | just (rename-def v' , _) = v'
...                                           | _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}

ctxt-rename : var → var → ctxt → ctxt
ctxt-rename v v' Γ @ (mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ) =
  (mk-ctxt (fn , mn , ps , qualif-insert-params q v' v ps) syms
  (trie-insert i v (rename-def v' , "missing" , "missing"))
  symb-occs Δ)

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- lookup mod params from filename
lookup-mod-params : ctxt → var → maybe params
lookup-mod-params (mk-ctxt _ (syms , _ , mn-ps , id) _ _ _) fn =
  trie-lookup syms fn ≫=maybe λ { (mn , _) →
  trie-lookup mn-ps mn }

-- look for a defined kind for the given var, which is assumed to be a type,
-- then instantiate its parameters
qual-lookup : ctxt → var → maybe (args × sym-info)
qual-lookup Γ@(mk-ctxt (_ , _ , _ , q) _ i _ _) v =
  trie-lookup q v ≫=maybe λ qv →
  trie-lookup i (fst qv) ≫=maybe λ si →
  just (snd qv , si)

env-lookup : ctxt → var → maybe sym-info
env-lookup Γ@(mk-ctxt (_ , _ , _ , _) _ i _ _) v =
  trie-lookup i v

-- look for a declared kind for the given var, which is assumed to be a type,
-- otherwise look for a qualified defined kind
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var Γ v with qual-lookup Γ v
... | just (as , type-decl k , _) = just k
... | just (as , type-def mps _ T k , _) = just (maybe-inst-kind Γ mps as k)
--... | just (as , datatype-def ps kᵢ k cs , _) = just (maybe-inst-kind Γ ps as k)
--... | just (as , mu-def mps x k , _) = just (maybe-inst-kind Γ mps as k)
... | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var Γ v with qual-lookup Γ v
... | just (as , term-decl T , _) = just T
... | just (as , term-def mps _ t T , _) = just $ maybe-inst-type Γ mps as T
... | just (as , ctr-def ps T _ _ _ , _) = just $ inst-type Γ ps as T
... | _ = nothing

ctxt-lookup-var : ctxt → var → maybe tk
ctxt-lookup-var Γ x with qual-lookup Γ x
-- terms
... | just (as , term-def mps _ t T , _)        = just ∘ Tkt $ maybe-inst-type Γ mps as T
... | just (as , term-decl T , _)               = just $ Tkt T
... | just (as , ctr-def ps T _ _ _ , _)       = just ∘ Tkt $ inst-type Γ ps as T
-- types
--... | just (as , datatype-def ps k₁ k cs , _)   = just ∘ Tkk $ maybe-inst-kind Γ ps as k
... | just (as , type-decl k , _)               = just $ Tkk k
... | just (as , type-def mps _ _ k , _)        = just ∘ Tkk $ maybe-inst-kind Γ mps as k
... | _                                         = nothing
-- ... | just (as , var-decl , _) = {!!}
-- ... | just (as , rename-def _ , _) = {!!}
-- ... | just (as , term-udef x₂ x₃ x₄ , x₁) = {!!}
-- ... | just (as , kind-def x₂ x₃ , x₁) = {!!}
-- ... | nothing = {!!}

ctxt-lookup-tk-var : ctxt → var → maybe tk
ctxt-lookup-tk-var Γ v with qual-lookup Γ v
... | just (as , term-decl T , _) = just $ Tkt T
... | just (as , type-decl k , _) = just $ Tkk k
... | just (as , term-def mps _ t T , _) = just $ Tkt $ maybe-inst-type Γ mps as T
... | just (as , type-def mps _ T k , _) = just $ Tkk $ maybe-inst-kind Γ mps as k
--... | just (as , datatype-def ps kᵢ k cs , _) = just $ Tkk $ maybe-inst-kind Γ ps as k
... | just (as , ctr-def ps T _ _ _ , _) = just $ Tkt $ inst-type Γ ps as T
... | _ = nothing

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def Γ v with env-lookup Γ v
... | just (term-def mps OpacTrans (just t) _ , _) = just $ maybe-else id lam-expand-term mps t
... | just (term-udef mps OpacTrans t , _) = just $ maybe-else id lam-expand-term mps t
... | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def Γ v with env-lookup Γ v
... | just (type-def mps OpacTrans (just T) _ , _) = just $ maybe-else id lam-expand-type mps T
... | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe (params × kind)
ctxt-lookup-kind-var-def Γ x with env-lookup Γ x
... | just (kind-def ps k , _) = just (ps , k)
... | _ = nothing

ctxt-lookup-kind-var-def-args : ctxt → var → maybe (params × args)
ctxt-lookup-kind-var-def-args Γ@(mk-ctxt (_ , _ , _ , q) _ i _ _) v with trie-lookup q v
... | just (v' , as) = ctxt-lookup-kind-var-def Γ v' ≫=maybe λ { (ps , k) → just (ps , as) }
... | _ = nothing

record ctxt-datatype-info : Set where
  constructor mk-data-info
  field
    name : var
    mu : maybe var
    asₚ : args
    asᵢ : 𝕃 tty
    ps : params
    kᵢ : kind
    k : kind
    cs : ctrs
    subst-cs : var → ctrs

data-lookup : ctxt → var → 𝕃 tty → maybe ctxt-datatype-info
data-lookup Γ @ (mk-ctxt mod ss is os (Δ , μ' , μ)) x as =
  maybe-else' (trie-lookup μ' x) -- Is x known locally to be a datatype?
    (trie-lookup Δ x ≫=maybe λ where -- No, so is it a global datatype?
      (ps , kᵢ , k , cs) →
        let asₚ = ttys-to-args-for-params nothing ps as
            asᵢ = drop (length ps) as in
        just $ mk-data-info x nothing asₚ asᵢ ps
          (inst-kind Γ ps asₚ kᵢ) (inst-kind Γ ps asₚ k) (inst-ctrs Γ ps asₚ cs)
          λ y → inst-ctrs Γ ps asₚ $ map (λ {(Ctr pi z T) → Ctr pi z $ subst Γ (lam-expand-type ps $ mtpvar y) x T}) cs) λ where
    (x' , x/mu , as') → -- Yes, it is a local datatype of x', as evinced by x/mu, and gives as' as parameters to x'
      trie-lookup Δ x' ≫=maybe λ where
      (ps , kᵢ , k , cs) →
        just $ mk-data-info x' (just x/mu) as' as ps
          (inst-kind Γ ps as' kᵢ) (inst-kind Γ ps as' k) (inst-ctrs Γ ps as' cs)
          λ y → inst-ctrs Γ ps as' $ map (λ {(Ctr pi z T) → Ctr pi z $ subst Γ (lam-expand-type ps $ mtpvar y) x' T}) cs

data-lookup-mu : ctxt → var → 𝕃 tty → maybe ctxt-datatype-info
data-lookup-mu Γ@(mk-ctxt mod ss is os (Δ , μ' , μ , η)) x as =
  trie-lookup μ x ≫=maybe λ x' → data-lookup Γ x' as

data-highlight : ctxt → var → ctxt
data-highlight (mk-ctxt mod ss is os (Δ , μ' , μ , η)) x =
  mk-ctxt mod ss is os (Δ , μ' , μ , stringset-insert η x)

ctxt-lookup-occurrences : ctxt → var → 𝕃 (var × posinfo × string)
ctxt-lookup-occurrences (mk-ctxt _ _ _ symb-occs _) symbol with trie-lookup symb-occs symbol
... | just l = l
... | nothing = []

ctxt-lookup-term-loc : ctxt → var → maybe location
ctxt-lookup-term-loc Γ x = qual-lookup Γ x ≫=maybe λ where
  (_ , term-decl _ , loc) → just loc
  (_ , term-def _ _ _ _ , loc) → just loc
  (_ , term-udef _ _ _ , loc) → just loc
  (_ , ctr-def _ _ _ _ _ , loc) → just loc
  (_ , var-decl , loc) → just loc
  _ → nothing

ctxt-lookup-type-loc : ctxt → var → maybe location
ctxt-lookup-type-loc Γ x = qual-lookup Γ x ≫=maybe λ where
  (_ , type-decl _ , loc) → just loc
  (_ , type-def _ _ _ _ , loc) → just loc
--  (_ , datatype-def _ _ _ _ , loc) → just loc
  (_ , var-decl , loc) → just loc
--  (_ , mu-def _ _ _ , loc) → just loc
  _ → nothing

----------------------------------------------------------------------

ctxt-var-location : ctxt → var → location
ctxt-var-location (mk-ctxt _ _ i _ _) x with trie-lookup i x
... | just (_ , l) = l
... | nothing = "missing" , "missing"

ctxt-clarify-def : ctxt → opacity → var → maybe (sym-info × ctxt)
ctxt-clarify-def Γ@(mk-ctxt mod@(_ , _ , _ , q) syms i sym-occurrences Δ) o x
  = trie-lookup i x ≫=maybe λ { (ci , l) →
    clarified x ci l }
  where
    ctxt' : var → ctxt-info → location → ctxt
    ctxt' v ci l = mk-ctxt mod syms (trie-insert i v (ci , l)) sym-occurrences Δ

    clarified : var → ctxt-info → location → maybe (sym-info × ctxt)
    clarified v ci@(term-def ps _ (just t) T) l = just ((ci , l) , (ctxt' v (term-def ps o (just t) T) l))
    clarified v ci@(term-udef ps _ t) l = just ((ci , l) , (ctxt' v (term-udef ps o t) l))
    clarified v ci@(type-def ps _ (just T) k) l = just ((ci , l) , (ctxt' v (type-def ps o (just T) k) l))
    clarified _ _ _ = nothing


ctxt-set-sym-info : ctxt → var → sym-info → ctxt
ctxt-set-sym-info (mk-ctxt mod syms i sym-occurrences Δ) x si =
  mk-ctxt mod syms (trie-insert i x si) sym-occurrences Δ

ctxt-restore-clarified-def : ctxt → var → sym-info → ctxt
ctxt-restore-clarified-def = ctxt-set-sym-info

ctxt-set-current-file : ctxt → string → string → ctxt
ctxt-set-current-file (mk-ctxt _ syms i symb-occs Δ) fn mn = mk-ctxt (fn , mn , [] , new-qualif) syms i symb-occs Δ

ctxt-set-current-mod : ctxt → mod-info → ctxt
ctxt-set-current-mod (mk-ctxt _ syms i symb-occs Δ) m = mk-ctxt m syms i symb-occs Δ

ctxt-add-current-params : ctxt → ctxt
ctxt-add-current-params Γ@(mk-ctxt m@(fn , mn , ps , _) (syms , mn-fn , mn-ps , ids) i symb-occs Δ) =
  mk-ctxt m (trie-insert syms fn (mn , []) , mn-fn , trie-insert mn-ps mn ps , ids) i symb-occs Δ

ctxt-clear-symbol : ctxt → string → ctxt
ctxt-clear-symbol Γ @ (mk-ctxt (fn , mn , pms , q) (syms , mn-fn) i symb-occs Δ) x =
  mk-ctxt (fn , mn , pms , (trie-remove q x)) (trie-map (λ ss → fst ss , remove _=string_ x (snd ss)) syms , mn-fn) (trie-remove i (qualif-var Γ x)) symb-occs Δ

ctxt-clear-symbols : ctxt → 𝕃 string → ctxt
ctxt-clear-symbols Γ [] = Γ
ctxt-clear-symbols Γ (v :: vs) = ctxt-clear-symbols (ctxt-clear-symbol Γ v) vs

ctxt-clear-symbols-of-file : ctxt → (filename : string) → ctxt
ctxt-clear-symbols-of-file (mk-ctxt f (syms , mn-fn , mn-ps) i symb-occs Δ) fn =
  mk-ctxt f (trie-insert syms fn (fst p , []) , trie-insert mn-fn (fst p) fn , mn-ps)
    (hremove i (fst p) (snd p))
    symb-occs Δ
  where
  p = trie-lookup𝕃2 syms fn
  hremove : ∀ {A : Set} → trie A → var → 𝕃 string → trie A
  hremove i mn [] = i
  hremove i mn (x :: xs) = hremove (trie-remove i (mn # x)) mn xs

ctxt-add-current-id : ctxt → ctxt
ctxt-add-current-id (mk-ctxt mod (syms , mn-fn , mn-ps , fn-ids , id , id-fns) is os Δ) =
  mk-ctxt mod (syms , mn-fn , mn-ps , trie-insert fn-ids (fst mod) (suc id) , suc id , (fst mod) :: id-fns) is os Δ

ctxt-initiate-file : ctxt → (filename modname : string) → ctxt
ctxt-initiate-file Γ fn mn = ctxt-add-current-id (ctxt-set-current-file (ctxt-clear-symbols-of-file Γ fn) fn mn)

unqual : ctxt → var → string
unqual (mk-ctxt (_ , _ , _ , q) _ _ _ _) v =
  if qualif-nonempty q
  then unqual-local (unqual-all q v)
  else v

qualified-ctxt : ctxt → ctxt
qualified-ctxt Γ @ (mk-ctxt mod ss is os Δ) =
  ctxt-set-qualif Γ $
    for trie-strings is accum empty-trie use λ x q →
      trie-insert q x (x , [])
