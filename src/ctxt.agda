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
new-ctxt fn mn =
  record {
    fn = fn;
    mn = mn;
    ps = [];
    qual = new-qualif;
    syms = empty-trie;
    mod-map = empty-trie;
    id-map = empty-trie;
    id-current = 0;
    id-list = [];
    i = empty-trie;
    μ = empty-trie;
    μ' = empty-trie;
    Is/μ = empty-trie;
    μ~ = empty-trie;
    μᵤ = nothing;
    μ̲ = empty-stringset
  }

empty-ctxt : ctxt
empty-ctxt = new-ctxt "" ""

ctxt-get-info : var → ctxt → maybe sym-info
ctxt-get-info v Γ = trie-lookup (ctxt.i Γ) v

ctxt-get-qi : ctxt → var → maybe qualif-info
ctxt-get-qi = trie-lookup ∘ ctxt.qual

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
ctxt-term-decl pi v T Γ =
  let v' =  pi % v in
  record Γ {
    qual = qualif-insert-params (ctxt.qual Γ) v' v [];
    i = trie-insert (ctxt.i Γ) v' (term-decl T , ctxt.fn Γ , pi)
  }

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl pi v k Γ =
  let v' = pi % v in
  record Γ {
    qual = qualif-insert-params (ctxt.qual Γ) v' v [];
    i = trie-insert (ctxt.i Γ) v' (type-decl k , ctxt.fn Γ , pi)
  }

ctxt-tk-decl : posinfo → var → tpkd → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ

infix 4 _,_-_:`_
_,_-_:`_ : ctxt → posinfo → var → tpkd → ctxt
Γ , pi - x :` tk = ctxt-tk-decl pi x tk Γ


-- TODO not sure how this and renaming interacts with module scope
ctxt-var-decl-if : var → ctxt → ctxt
ctxt-var-decl-if v Γ with trie-lookup (ctxt.i Γ) v
... | just (rename-def _ , _) = Γ
... | just (var-decl , _) = Γ
... | _ = ctxt-var-decl v Γ

add-indices-to-ctxt : indices → ctxt → ctxt
add-indices-to-ctxt = flip $ foldr λ {(Index x _) → ctxt-var-decl x}

add-params-to-ctxt : params → ctxt → ctxt
add-params-to-ctxt = flip $ foldr λ {(Param me x _) Γ → if ctxt-binds-var Γ (unqual-local x) then Γ else (ctxt-var-decl x ∘ ctxt-var-decl (unqual-local x)) Γ}

add-caseArgs-to-ctxt : case-args → ctxt → ctxt
add-caseArgs-to-ctxt = flip $ foldr λ {(CaseArg me x _) → ctxt-var-decl x}

add-ctrs-to-ctxt : ctrs → ctxt → ctxt
add-ctrs-to-ctxt = flip $ foldr λ {(Ctr x T) → ctxt-var-decl x}

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep Γ v with trie-lookup (ctxt.i Γ) v 
...| just (rename-def v' , _) = v'
...| _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}

ctxt-rename : var → var → ctxt → ctxt
ctxt-rename v v' Γ =
  record Γ {
    qual = trie-insert (ctxt.qual Γ) v (v' , []);
    i = trie-insert (ctxt.i Γ) v (rename-def v' , missing-location)
  }

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- lookup mod params from filename
lookup-mod-params : ctxt → var → maybe params
lookup-mod-params Γ fn =
  trie-lookup (ctxt.syms Γ) fn >>=c λ mn _ →
  trie-lookup (ctxt.mod-map Γ) mn >>=c λ fn' → just

-- look for a defined kind for the given var, which is assumed to be a type,
-- then instantiate its parameters
qual-lookup : ctxt → var → maybe (var × args × sym-info)
qual-lookup Γ v =
  trie-lookup (ctxt.qual Γ) v >>=c λ qv as →
  trie-lookup (ctxt.i Γ) qv >>= λ si →
  just (qv , as , si)

env-lookup : ctxt → var → maybe sym-info
env-lookup = trie-lookup ∘ ctxt.i

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

{-
inst-enc-defs : ctxt → params → args → encoding-defs → encoding-defs
inst-enc-defs Γ ps as (mk-enc-defs ecs gcs Cast cast-in cast-out cast-is Functor functor-in functor-out Fix fix-in fix-out lambek1 lambek2 fix-ind) =
  let as = arg-set-erased tt <$> as in
  mk-enc-defs ecs gcs
    (inst-type Γ ps as Cast)
    (inst-term Γ ps as cast-in)
    (inst-term Γ ps as cast-out)
    (inst-term Γ ps as cast-is)
    (inst-type Γ ps as Functor)
    (inst-term Γ ps as functor-in)
    (inst-term Γ ps as functor-out)
    (inst-type Γ ps as Fix)
    (inst-term Γ ps as fix-in)
    (inst-term Γ ps as fix-out)
    (inst-term Γ ps as lambek1)
    (inst-term Γ ps as lambek2)
    (inst-term Γ ps as fix-ind)
-}

data-lookup' : ctxt → var → var → 𝕃 tmtp → maybe datatype-info
data-lookup' Γ xₒ x as =
  (maybe-else'
    {B = maybe (var × args × 𝕃 tmtp ×
                 params × kind × kind × ctrs × encoding-defs × encoded-defs)}
    (trie-lookup (ctxt.μ' Γ) x) -- Is x known locally to be a datatype?
    (trie-lookup (ctxt.μ Γ) x >>=c λ ps rest → -- No, so is it a global datatype?
      let asₚ = tmtps-to-args-for-params nothing ps as
          asᵢ = drop (length ps) as in
      just (x , asₚ , asᵢ , ps , rest))
   λ where
    (x' , as') → -- Yes, it is a local datatype of x', and gives as' as parameters to x'
      trie-lookup (ctxt.μ Γ) x' >>= λ rest → just (x' , as' , as , rest))
  >>= λ where
    (x' , asₚ , asᵢ , ps , kᵢ , k , cs , eds , gds) →
      just $ mk-data-info x' xₒ asₚ asᵢ ps
        (inst-kind Γ ps asₚ kᵢ)
        (inst-kind Γ ps asₚ k)
        cs
        (inst-ctrs Γ ps asₚ (map-snd (subst Γ (params-to-tpapps ps (TpVar x')) x') <$> cs))
        eds {-(inst-enc-defs Γ ps asₚ eds)-}
        gds
        --λ y → inst-ctrs Γ ps asₚ (map-snd (rename-var {TYPE} Γ x' y) <$> cs)

data-lookup : ctxt → var → 𝕃 tmtp → maybe datatype-info
data-lookup Γ x = data-lookup' Γ x x

data-lookup-mu : ctxt → var → var → 𝕃 tmtp → maybe datatype-info
data-lookup-mu Γ xₒ x as =
  trie-lookup (ctxt.Is/μ Γ) x >>= λ x' → data-lookup' Γ xₒ x' as

data-highlight : ctxt → var → ctxt
data-highlight Γ x = record Γ { μ̲ = stringset-insert (ctxt.μ̲ Γ) x }


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
ctxt-var-location Γ x with trie-lookup (ctxt.i Γ) x
... | just (_ , l) = l
... | nothing = missing-location

ctxt-clarify-def : ctxt → opacity → var → maybe ctxt
ctxt-clarify-def Γ o x with qual-lookup Γ x
...| just (qx , as , type-def ps o' T? k , loc) =
  ifMaybej (o xor o') (record Γ { i = trie-insert (ctxt.i Γ) qx (type-def ps o T? k , loc) })
...| just (qx , as , term-def ps o' t? T , loc) =
  ifMaybej (o xor o') (record Γ { i = trie-insert (ctxt.i Γ) qx (term-def ps o t? T , loc) })
...| just (qx , as , term-udef ps o' t , loc) =
  ifMaybej (o xor o') (record Γ { i = trie-insert (ctxt.i Γ) qx (term-udef ps o t , loc) })
...| _ = nothing

ctxt-set-current-file : ctxt → string → string → ctxt
ctxt-set-current-file Γ fn mn = record Γ { fn = fn; mn = mn; ps = []; qual = new-qualif }

ctxt-set-current-mod : ctxt → string × string × params × qualif → ctxt
ctxt-set-current-mod Γ (fn , mn , ps , qual) = record Γ { fn = fn; mn = mn; ps = ps; qual = qual }

ctxt-add-current-params : ctxt → ctxt
ctxt-add-current-params Γ =
  record Γ {
    syms = trie-insert (ctxt.syms Γ) (ctxt.fn Γ) (ctxt.mn Γ , []);
    mod-map = trie-insert (ctxt.mod-map Γ) (ctxt.mn Γ) (ctxt.fn Γ , ctxt.ps Γ)
  }

ctxt-clear-symbol : ctxt → string → ctxt
ctxt-clear-symbol Γ x =
  let qx = qualif-var Γ x in
  record Γ {
    qual = trie-remove (ctxt.qual Γ) x;
    syms = trie-map (λ ss → fst ss , remove _=string_ x (snd ss)) (ctxt.syms Γ);
    i = trie-remove (ctxt.i Γ) qx;
    μ = trie-remove (ctxt.μ Γ) qx;
    Is/μ = trie-remove (ctxt.Is/μ Γ) qx;
    μ̲ = trie-remove (ctxt.μ̲ Γ) qx
  }

ctxt-clear-symbols : ctxt → 𝕃 string → ctxt
ctxt-clear-symbols Γ [] = Γ
ctxt-clear-symbols Γ (v :: vs) = ctxt-clear-symbols (ctxt-clear-symbol Γ v) vs

ctxt-clear-symbols-of-file : ctxt → (filename : string) → ctxt
ctxt-clear-symbols-of-file Γ fn =
  elim-pair (trie-lookup𝕃2 (ctxt.syms Γ) fn) λ mn xs →
  let ps = maybe-else' (trie-lookup (ctxt.mod-map Γ) mn) [] snd in
  record Γ {
    syms = trie-insert (ctxt.syms Γ) fn (mn , []);
    mod-map = trie-insert (ctxt.mod-map Γ) mn (fn , ps);
    i = hremove (ctxt.i Γ) mn xs;
    μ = hremove (ctxt.μ Γ) mn xs;
    Is/μ = hremove (ctxt.Is/μ Γ) mn xs;
    μ̲ = hremove (ctxt.μ̲ Γ) mn xs
  }
  where
  hremove : ∀ {A : Set} → trie A → var → 𝕃 string → trie A
  hremove i mn [] = i
  hremove i mn (x :: xs) = hremove (trie-remove i (mn # x)) mn xs

ctxt-add-current-id : ctxt → ctxt
ctxt-add-current-id Γ with trie-contains (ctxt.id-map Γ) (ctxt.fn Γ)
...| tt = Γ
...| ff =
  record Γ {
    id-map = trie-insert (ctxt.id-map Γ) (ctxt.fn Γ) (suc (ctxt.id-current Γ));
    id-current = suc (ctxt.id-current Γ);
    id-list = ctxt.fn Γ :: ctxt.id-list Γ
  }

ctxt-initiate-file : ctxt → (filename modname : string) → ctxt
ctxt-initiate-file Γ fn mn = ctxt-add-current-id (ctxt-set-current-file (ctxt-clear-symbols-of-file Γ fn) fn mn)

unqual : ctxt → var → string
unqual Γ v =
  if qualif-nonempty (ctxt.qual Γ)
  then unqual-local (unqual-all (ctxt.qual Γ) v)
  else v

qualified-ctxt : ctxt → ctxt
qualified-ctxt Γ = -- use ctxt.i so we bring ALL defs (even from cousin modules, etc...) into scope
  record Γ {qual = for trie-strings (ctxt.i Γ) accum empty-trie use λ x q → trie-insert q x (x , [])}
