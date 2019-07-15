module ctxt where

open import cedille-types
open import ctxt-types public
open import subst
open import general-util
open import syntax-util
open import type-util
open import free-vars

new-sym-info-trie : trie sym-info
new-sym-info-trie = trie-insert empty-trie compileFail-qual ((term-decl compileFailType) , "missing" , "missing")

new-qualif : qualif
new-qualif = trie-insert empty-trie compileFail (compileFail-qual , [])

qualif-nonempty : qualif → 𝔹
qualif-nonempty q = trie-nonempty (trie-remove q compileFail)

qualif-insert-params : qualif → var → var → params → qualif
qualif-insert-params σ qv v ps = trie-insert σ v (qv , params-to-args ps)

qualif-insert-import : qualif → var → maybe import-as → 𝕃 string → args → qualif
qualif-insert-import σ mn oa [] as = σ
qualif-insert-import σ mn oa (v :: vs) as = qualif-insert-import (trie-insert σ (maybe-else v (λ {(ImportAs _ pfx) → pfx # v}) oa) (mn # v , as)) mn oa vs as


new-ctxt : (filename modname : string) → ctxt
new-ctxt fn mn = mk-ctxt (fn , mn , [] , new-qualif) (empty-trie , empty-trie , empty-trie , empty-trie , 0 , []) new-sym-info-trie (empty-trie , empty-trie , empty-trie , [] , empty-trie)

empty-ctxt : ctxt
empty-ctxt = new-ctxt "" ""

ctxt-get-info : var → ctxt → maybe sym-info
ctxt-get-info v (mk-ctxt _ _ i _) = trie-lookup i v

ctxt-set-qualif : ctxt → qualif → ctxt
ctxt-set-qualif (mk-ctxt (f , m , p , q') syms i Δ) q
  = mk-ctxt (f , m , p , q) syms i Δ

ctxt-get-qualif : ctxt → qualif
ctxt-get-qualif (mk-ctxt (_ , _ , _ , q) _ _ _) = q

ctxt-get-qi : ctxt → var → maybe qualif-info
ctxt-get-qi Γ = trie-lookup (ctxt-get-qualif Γ)

ctxt-qualif-args-length : ctxt → erased? → var → maybe ℕ
ctxt-qualif-args-length Γ me v =
  ctxt-get-qi Γ v >>= λ qv →
  just (if me then length (snd qv) else length (erase-args (snd qv)))

qi-var-if : maybe qualif-info → var → var
qi-var-if (just (v , _)) _ = v
qi-var-if nothing v = v

--ctxt-restore-info : ctxt → var → maybe qualif-info → maybe sym-info → ctxt
--ctxt-restore-info (mk-ctxt (fn , mn , ps , q , ) syms i Δ) v qi si =
--  mk-ctxt (fn , mn , ps , f qi v q) syms (f si (qi-var-if qi v) (trie-remove i (qi-var-if (trie-lookup q v) v))) Δ
--  where
--    f : ∀{A : Set} → maybe A → string → trie A → trie A
--    f (just a) s t = trie-insert t s a
--    f nothing s t = trie-remove t s

--ctxt-restore-info* : ctxt → 𝕃 (string × maybe qualif-info × maybe sym-info) → ctxt
--ctxt-restore-info* Γ [] = Γ
--ctxt-restore-info* Γ ((v , qi , m) :: ms) = ctxt-restore-info* (ctxt-restore-info Γ v qi m) ms

def-params : defScope → params → defParams
def-params tt ps = nothing
def-params ff ps = just ps

inst-term : ctxt → params → args → term → term
inst-term Γ ps as t with subst-params-args ps as
...| σ , ps' , as' = lam-expand-term (substs-params Γ σ ps') (substs Γ σ t)

-- TODO add renamectxt to avoid capture bugs?
inst-type : ctxt → params → args → type → type
inst-type Γ ps as T with subst-params-args ps as
...| σ , ps' , as' = abs-expand-type (substs-params Γ σ ps') (substs Γ σ T)

inst-kind : ctxt → params → args → kind → kind
inst-kind Γ ps as k with subst-params-args ps as
...| σ , ps' , as' = abs-expand-kind (substs-params Γ σ ps') (substs Γ σ k)

inst-ctrs : ctxt → params → args → ctrs → ctrs
inst-ctrs Γ ps as c with subst-params-args ps as
...| σ , ps' , as' = flip map c λ where
  (Ctr x T) → Ctr x (abs-expand-type (substs-params Γ σ ps') (substs Γ σ T))

maybe-inst-type = maybe-else (λ as T → T) ∘ inst-type
maybe-inst-kind = maybe-else (λ as T → T) ∘ inst-kind
maybe-inst-ctrs = maybe-else (λ as c → c) ∘ inst-ctrs

ctxt-term-decl : posinfo → var → type → ctxt → ctxt
ctxt-term-decl p v T Γ@(mk-ctxt (fn , mn , ps , q) syms i Δ) =
  let v' =  p % v in
  mk-ctxt (fn , mn , ps , qualif-insert-params q v' v [])
    syms (trie-insert i v' (term-decl T , fn , p)) Δ

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl p v k Γ@(mk-ctxt (fn , mn , ps , q) syms i Δ) =
  let v' = p % v in
  mk-ctxt (fn , mn , ps , qualif-insert-params q v' v [])
    syms (trie-insert i v' (type-decl k , fn , p)) Δ

ctxt-tk-decl : posinfo → var → tpkd → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ

infix 4 _,_-_:`_
_,_-_:`_ : ctxt → posinfo → var → tpkd → ctxt
Γ , pi - x :` tk = ctxt-tk-decl pi x tk Γ


-- TODO not sure how this and renaming interacts with module scope
ctxt-var-decl-if : var → ctxt → ctxt
ctxt-var-decl-if v Γ with Γ
... | mk-ctxt (fn , mn , ps , q) syms i Δ with trie-lookup i v
... | just (rename-def _ , _) = Γ
... | just (var-decl , _) = Γ
... | _ = mk-ctxt (fn , mn , ps , trie-insert q v (v , [])) syms
  (trie-insert i v (var-decl , "missing" , "missing")) Δ

add-indices-to-ctxt : indices → ctxt → ctxt
add-indices-to-ctxt = flip $ foldr λ {(Index x _) → ctxt-var-decl x}

add-params-to-ctxt : params → ctxt → ctxt
add-params-to-ctxt = flip $ foldr λ {(Param me x _) → ctxt-var-decl x}

add-caseArgs-to-ctxt : case-args → ctxt → ctxt
add-caseArgs-to-ctxt = flip $ foldr λ {(CaseArg me x _) → ctxt-var-decl x}

add-ctrs-to-ctxt : ctrs → ctxt → ctxt
add-ctrs-to-ctxt = flip $ foldr λ {(Ctr x T) → ctxt-var-decl x}

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt m syms i _) v with trie-lookup i v 
...                                           | just (rename-def v' , _) = v'
...                                           | _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}

ctxt-rename : var → var → ctxt → ctxt
ctxt-rename v v' Γ @ (mk-ctxt (fn , mn , ps , q) syms i Δ) =
  mk-ctxt (fn , mn , ps , qualif-insert-params q v' v ps) syms
    (trie-insert i v (rename-def v' , "missing" , "missing")) Δ

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- lookup mod params from filename
lookup-mod-params : ctxt → var → maybe params
lookup-mod-params (mk-ctxt _ (syms , _ , mn-ps , id) _ _) fn =
  trie-lookup syms fn >>= λ { (mn , _) →
  trie-lookup mn-ps mn }

-- look for a defined kind for the given var, which is assumed to be a type,
-- then instantiate its parameters
qual-lookup : ctxt → var → maybe (var × args × sym-info)
qual-lookup Γ@(mk-ctxt (_ , _ , _ , q) _ i _) v =
  trie-lookup q v >>= λ qv →
  trie-lookup i (fst qv) >>= λ si →
  just (fst qv , snd qv , si)

env-lookup : ctxt → var → maybe sym-info
env-lookup Γ@(mk-ctxt (_ , _ , _ , _) _ i _) v =
  trie-lookup i v

ctxt-lookup-tpkd-var : ctxt → var → maybe (var × args × tpkd)
ctxt-lookup-tpkd-var Γ v with qual-lookup Γ v
... | just (qv , as , term-decl T , _) = just $ qv , as , Tkt T
... | just (qv , as , type-decl k , _) = just $ qv , as , Tkk k
... | just (qv , as , term-def mps _ t T , _) = just $ qv , as , Tkt (maybe-inst-type Γ mps as T)
... | just (qv , as , ctr-def ps T _ _ _ , _) = just $ qv , as , Tkt (inst-type Γ ps as T)
... | just (qv , as , type-def mps _ T k , _) = just $ qv , as , Tkk (maybe-inst-kind Γ mps as k)
... | _ = nothing

ctxt-lookup-type-var : ctxt → var → maybe (var × args × kind)
ctxt-lookup-type-var Γ v = ctxt-lookup-tpkd-var Γ v >>= λ where
  (qv , as , Tkt T) → nothing
  (qv , as , Tkk k) → just (qv , as , k)

ctxt-lookup-term-var : ctxt → var → maybe (var × args × type)
ctxt-lookup-term-var Γ v = ctxt-lookup-tpkd-var Γ v >>= λ where
  (qv , as , Tkt T) → just (qv , as , T)
  (qv , as , Tkk k) → nothing

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def Γ v with env-lookup Γ v
... | just (term-def mps opacity-open (just t) _ , _) = just $ maybe-else id lam-expand-term mps t
... | just (term-udef mps opacity-open t , _) = just $ maybe-else id lam-expand-term mps t
... | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def Γ v with env-lookup Γ v
... | just (type-def mps opacity-open (just T) _ , _) = just $ maybe-else id lam-expand-type mps T
... | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe (params × kind)
ctxt-lookup-kind-var-def Γ x with qual-lookup Γ x
...| just (_ , as , kind-def ps k , _) = case subst-params-args' Γ ps as k of λ where
  (k' , ps' , as') → just (ps' , k')
...| _ = nothing

ctxt-binds-term-var : ctxt → var → maybe (var × args)
ctxt-binds-term-var Γ x with qual-lookup Γ x
...| just (qx , as , term-def _ _ _ _ , _) = just (qx , as)
...| just (qx , as , term-udef _ _ _ , _) = just (qx , as)
...| just (qx , as , term-decl _ , _) = just (qx , as)
...| just (qx , as , ctr-def _ _ _ _ _ , _) = just (qx , as)
--...| just (qx , as , var-decl , _) = just (qx , as)
...| _ = nothing

ctxt-binds-type-var : ctxt → var → maybe (var × args)
ctxt-binds-type-var Γ x with qual-lookup Γ x
...| just (qx , as , type-def _ _ _ _ , _) = just (qx , as)
...| just (qx , as , type-decl _ , _) = just (qx , as)
...| _ = nothing

record ctxt-datatype-info : Set where
  constructor mk-data-info
  field
    name : var
    mu : maybe term
    asₚ : args
    asᵢ : 𝕃 tmtp
    ps : params
    kᵢ : kind
    k : kind
    cs : ctrs
    eds : encoding-defs
    gds : encoded-defs
    subst-cs : var → ctrs

inst-enc-defs : ctxt → args → encoding-defs → encoding-defs
inst-enc-defs Γ as (mk-enc-defs ecs gcs Cast cast-in cast-out cast-is Functor functor-in functor-out Fix fix-in fix-out lambek1 lambek2 fix-ind) =
  let as = arg-set-erased tt <$> as
      bs = args-to-tmtps as in
  mk-enc-defs ecs gcs
    (recompose-tpapps bs Cast)
    (recompose-apps   as cast-in)
    (recompose-apps   as cast-out)
    (recompose-apps   as cast-is)
    (recompose-tpapps bs Functor)
    (recompose-apps   as functor-in)
    (recompose-apps   as functor-out)
    (recompose-tpapps bs Fix)
    (recompose-apps   as fix-in)
    (recompose-apps   as fix-out)
    (recompose-apps   as lambek1)
    (recompose-apps   as lambek2)
    (recompose-apps   as fix-ind)

data-lookup : ctxt → var → 𝕃 tmtp → maybe ctxt-datatype-info
data-lookup Γ @ (mk-ctxt mod ss is (Δ , μ' , μ)) x as =
  (maybe-else'
    {B = maybe (var × maybe term × args × 𝕃 tmtp ×
                 params × kind × kind × ctrs × encoding-defs × encoded-defs)}
    (trie-lookup μ' x) -- Is x known locally to be a datatype?
    (trie-lookup Δ x >>=c λ ps rest → -- No, so is it a global datatype?
      let asₚ = tmtps-to-args-for-params nothing ps as
          asᵢ = drop (length ps) as in
      just (x , nothing , asₚ , asᵢ , ps , rest))
   λ where
    (x' , x/mu , as') → -- Yes, it is a local datatype of x', as evinced by x/mu, and gives as' as parameters to x'
      trie-lookup Δ x' >>= λ rest → just (x' , just (Var x/mu) , as' , as , rest))
  >>= λ where
    (x' , x/mu , asₚ , asᵢ , ps , kᵢ , k , cs , eds , gds) →
      just $ mk-data-info x' x/mu asₚ asᵢ ps
        (inst-kind Γ ps asₚ kᵢ)
        (inst-kind Γ ps asₚ k)
        (inst-ctrs Γ ps asₚ (map-snd (subst Γ (params-to-tpapps ps (TpVar x')) x') <$> cs))
        (inst-enc-defs Γ asₚ eds)
        gds
        λ y → inst-ctrs Γ ps asₚ (map-snd (rename-var {TYPE} Γ x' y) <$> cs)

data-lookup-mu : ctxt → var → 𝕃 tmtp → maybe ctxt-datatype-info
data-lookup-mu Γ@(mk-ctxt mod ss is (Δ , μ' , μ , η)) x as =
  trie-lookup μ x >>= λ x' → data-lookup Γ x' as

data-highlight : ctxt → var → ctxt
data-highlight (mk-ctxt mod ss is (Δ , μ' , μ , μ~ , η)) x =
  mk-ctxt mod ss is (Δ , μ' , μ , μ~ , stringset-insert η x)


ctxt-lookup-term-loc : ctxt → var → maybe location
ctxt-lookup-term-loc Γ x = qual-lookup Γ x >>= λ where
  (_ , _ , term-decl _ , loc) → just loc
  (_ , _ , term-def _ _ _ _ , loc) → just loc
  (_ , _ , term-udef _ _ _ , loc) → just loc
  (_ , _ , ctr-def _ _ _ _ _ , loc) → just loc
  (_ , _ , var-decl , loc) → just loc
  _ → nothing

ctxt-lookup-type-loc : ctxt → var → maybe location
ctxt-lookup-type-loc Γ x = qual-lookup Γ x >>= λ where
  (_ , _ , type-decl _ , loc) → just loc
  (_ , _ , type-def _ _ _ _ , loc) → just loc
  (_ , _ , var-decl , loc) → just loc
  _ → nothing

----------------------------------------------------------------------

ctxt-var-location : ctxt → var → location
ctxt-var-location (mk-ctxt _ _ i _) x with trie-lookup i x
... | just (_ , l) = l
... | nothing = "missing" , "missing"

ctxt-clarify-def : ctxt → opacity → var → maybe ctxt
ctxt-clarify-def Γ o x with qual-lookup Γ x
...| just (qx , as , type-def ps o' T? k , loc) =
  maybe-if (o xor o') >>
  just (record Γ { i = trie-insert (ctxt.i Γ) qx (type-def ps o T? k , loc) })
...| just (qx , as , term-def ps o' t? T , loc) =
  maybe-if (o xor o') >>
  just (record Γ { i = trie-insert (ctxt.i Γ) qx (term-def ps o t? T , loc) })
...| just (qx , as , term-udef ps o' t , loc) =
  maybe-if (o xor o') >>
  just (record Γ { i = trie-insert (ctxt.i Γ) qx (term-udef ps o t , loc) })
...| _ = nothing

ctxt-set-current-file : ctxt → string → string → ctxt
ctxt-set-current-file Γ fn mn = record Γ { mod = fn , mn , [] , new-qualif }

ctxt-set-current-mod : ctxt → mod-info → ctxt
ctxt-set-current-mod (mk-ctxt _ syms i Δ) m = mk-ctxt m syms i Δ

ctxt-set-current-params : ctxt → params → ctxt
ctxt-set-current-params (mk-ctxt (fn , mn , ps , q) ss is Δ) ps' = mk-ctxt (fn , mn , ps' , q) ss is Δ

ctxt-add-current-params : ctxt → ctxt
ctxt-add-current-params Γ@(mk-ctxt m@(fn , mn , ps , _) (syms , mn-fn , mn-ps , ids) i Δ) =
  mk-ctxt m (trie-insert syms fn (mn , []) , mn-fn , trie-insert mn-ps mn ps , ids) i Δ

ctxt-clear-symbol : ctxt → string → ctxt
ctxt-clear-symbol Γ @ (mk-ctxt (fn , mn , pms , q) (syms , mn-fn) i Δ) x =
  mk-ctxt (fn , mn , pms , trie-remove q x) (trie-map (λ ss → fst ss , remove _=string_ x (snd ss)) syms , mn-fn) (trie-remove i (qualif-var Γ x)) Δ

ctxt-clear-symbols : ctxt → 𝕃 string → ctxt
ctxt-clear-symbols Γ [] = Γ
ctxt-clear-symbols Γ (v :: vs) = ctxt-clear-symbols (ctxt-clear-symbol Γ v) vs

ctxt-clear-symbols-of-file : ctxt → (filename : string) → ctxt
ctxt-clear-symbols-of-file (mk-ctxt f (syms , mn-fn , mn-ps) i Δ) fn =
  mk-ctxt f (trie-insert syms fn (fst p , []) , trie-insert mn-fn (fst p) fn , mn-ps)
    (hremove i (fst p) (snd p)) Δ
  where
  p = trie-lookup𝕃2 syms fn
  hremove : ∀ {A : Set} → trie A → var → 𝕃 string → trie A
  hremove i mn [] = i
  hremove i mn (x :: xs) = hremove (trie-remove i (mn # x)) mn xs

ctxt-add-current-id : ctxt → ctxt
ctxt-add-current-id Γ @ (mk-ctxt mod (syms , mn-fn , mn-ps , fn-ids , id , id-fns) is Δ) with trie-contains fn-ids (fst mod)
...| tt = Γ
...| ff = mk-ctxt mod (syms , mn-fn , mn-ps ,
                trie-insert fn-ids (fst mod) (suc id) , suc id , (fst mod) :: id-fns) is Δ

ctxt-initiate-file : ctxt → (filename modname : string) → ctxt
ctxt-initiate-file Γ fn mn = ctxt-add-current-id (ctxt-set-current-file (ctxt-clear-symbols-of-file Γ fn) fn mn)

unqual : ctxt → var → string
unqual (mk-ctxt (_ , _ , _ , q) _ _ _) v =
  if qualif-nonempty q
  then unqual-local (unqual-all q v)
  else v

qualified-ctxt : ctxt → ctxt
qualified-ctxt Γ @ (mk-ctxt mod ss is Δ) =
  ctxt-set-qualif Γ $
    for trie-strings is accum empty-trie use λ x q →
      trie-insert q x (x , [])
