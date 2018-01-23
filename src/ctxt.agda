module ctxt where

open import lib
open import cedille-types
open import ctxt-types public
open import subst
open import general-util
open import syntax-util

new-ctxt : (filename modname : string) → ctxt
new-ctxt fn mn = mk-ctxt (fn , mn , ParamsNil , empty-trie) empty-trie empty-trie empty-trie

ctxt-get-info : var → ctxt → maybe sym-info
ctxt-get-info v (mk-ctxt _ _ i _) = trie-lookup i v

ctxt-restore-info : ctxt → string → maybe sym-info → ctxt
ctxt-restore-info (mk-ctxt f syms i symb-occs) x nothing = mk-ctxt f syms (trie-remove i x) symb-occs
ctxt-restore-info (mk-ctxt f syms i symb-occs) x (just n) = mk-ctxt f syms (trie-insert i x n) symb-occs

ctxt-restore-info* : ctxt → 𝕃 (string × maybe sym-info) → ctxt
ctxt-restore-info* Γ [] = Γ
ctxt-restore-info* Γ ((x , m) :: ms) = ctxt-restore-info* (ctxt-restore-info Γ x m) ms

ctxt-term-decl : posinfo → var → type → ctxt → ctxt
ctxt-term-decl p v t (mk-ctxt (fn , ps , q) syms i symb-occs) = mk-ctxt (fn , ps , q)
                                                    syms
                                                    (trie-insert i v (term-decl t , (fn , p)))
                                                    symb-occs

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl p v k (mk-ctxt (fn , ps , q) syms i symb-occs) = mk-ctxt (fn , ps , q)
                                                    syms
                                                    (trie-insert i v (type-decl k , (fn , p)))
                                                    symb-occs

def-params : defScope → params → defParams
def-params tt ps = nothing
def-params ff ps = just ps

-- TODO add renamectxt to avoid capture bugs?
inst-type : ctxt → params → args → type → type
inst-type Γ ps as = substs-type Γ (mk-inst ps as)

inst-kind : ctxt → params → args → kind → kind
inst-kind Γ ps as = substs-kind Γ (mk-inst ps as)

-- TODO substs-params
inst-params : ctxt → params → args → params → params
inst-params Γ ps as qs = qs

qualif-term : ctxt → term → term
qualif-term Γ@(mk-ctxt (_ , _ , _ , σ) _ _ _) = substs-term Γ σ

qualif-type : ctxt → type → type
qualif-type Γ@(mk-ctxt (_ , _ , _ , σ) _ _ _) = substs-type Γ σ

qualif-kind : ctxt → kind → kind
qualif-kind Γ@(mk-ctxt (_ , _ , _ , σ) _ _ _) = substs-kind Γ σ

qualif-tk : ctxt → tk → tk
qualif-tk Γ (Tkt t) = Tkt (qualif-type Γ t)
qualif-tk Γ (Tkk k) = Tkk (qualif-kind Γ k)

ctxt-kind-def : posinfo → var → params → kind → ctxt → ctxt
ctxt-kind-def p v ps2 k (mk-ctxt (fn , mn , ps1 , q) syms i symb-occs) = mk-ctxt
  (fn , mn , ps1 , qualif-insert-params q mn v ps1)
  (trie-insert-append2 syms fn mn v)
  (trie-insert i (mn # v) (kind-def ps1 ps2 k , (fn , p)))
  symb-occs

ctxt-type-def : posinfo → defScope → var → type → kind → ctxt → ctxt
ctxt-type-def p s v t k Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q mn v ps)
  (if (s iff localScope) then syms else trie-insert-append2 syms fn mn v)
  (trie-insert i v' (type-def (def-params s ps) t k , (fn , p)))
  symb-occs
  where v' = if s iff localScope then v else mn # v

ctxt-term-def : posinfo → defScope → var → term → type → ctxt → ctxt
ctxt-term-def p s v t tp Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q mn v ps)
  (if (s iff localScope) then syms else trie-insert-append2 syms fn mn v)
  (trie-insert i v' (term-def (def-params s ps) t tp , (fn , p)))
  symb-occs
  where v' = if s iff localScope then v else mn # v

ctxt-term-udef : posinfo → defScope → var → term → ctxt → ctxt
ctxt-term-udef p s v t Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q mn v ps)
  (if (s iff localScope) then syms else trie-insert-append2 syms fn mn v)
  (trie-insert i (mn # v) (term-udef (def-params s ps) t , (fn , p)))
  symb-occs

-- TODO not sure how this and renaming interacts with module scope
ctxt-var-decl-if : posinfo → var → ctxt → ctxt
ctxt-var-decl-if p v Γ with Γ
... | mk-ctxt (fn , mn , ps , q) syms i symb-occs with trie-lookup i v
... | just (rename-def _ , _) = Γ
... | just (var-decl , _) = Γ
... | _ = mk-ctxt (fn , mn , ps , q) syms
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
ctxt-rename p v v' (mk-ctxt (fn , ps , q) syms i symb-occs) = 
  (mk-ctxt (fn , ps , q) syms
      (trie-insert i v (rename-def v' , (fn , p)))
      symb-occs)

ctxt-tk-decl : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ 

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- look for a defined kind for the given var, which is assumed to be a type,
-- then instantiate its parameters
env-lookup-type-var : ctxt → var → args → maybe kind
env-lookup-type-var Γ@(mk-ctxt _ _ i _) v as with trie-lookup i v
... | just (type-def (just ps) _ k , _) = just (inst-kind Γ ps as k)
... | _ = nothing

-- look for a declared kind for the given var, which is assumed to be a type,
-- otherwise look for a qualified defined kind
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var Γ@(mk-ctxt (_ , _ , _ , q) _ i _) v with trie-lookup i v
... | just (type-decl k , _) = just (qualif-kind Γ k)
... | just (type-def nothing _ k , _) = just (qualif-kind Γ k)
... | _ with trie-lookup q v
... | just (v' , as) = env-lookup-type-var Γ v' as
... | _ = nothing

env-lookup-term-var : ctxt → var → args → maybe type
env-lookup-term-var Γ@(mk-ctxt _ _ i _) v as with trie-lookup i v
... | just (term-def (just ps) _ t , _) = just (inst-type Γ ps as t)
... | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var Γ@(mk-ctxt (_ , _ , _ , q) _ i _) v with trie-lookup i v
... | just (term-decl t , _) = just (qualif-type Γ t)
... | just (term-def nothing _ t , _) = just (qualif-type Γ t)
... | _ with trie-lookup q v
... | just (v' , as) = env-lookup-term-var Γ v' as
... | _ = nothing

env-lookup-tk-var : ctxt → var → args → maybe tk
env-lookup-tk-var Γ@(mk-ctxt _ _ i _) v as with trie-lookup i v
... | just (type-def (just ps) _ k , _) = just (Tkk (inst-kind Γ ps as k))
... | just (term-def (just ps) _ t , _) = just (Tkt (inst-type Γ ps as t))
... | _ = nothing

ctxt-lookup-tk-var : ctxt → var → maybe tk
ctxt-lookup-tk-var Γ@(mk-ctxt (_ , _ , _ , q) _ i _) v with trie-lookup i v
... | just (type-decl k , _) = just (Tkk (qualif-kind Γ k))
... | just (type-def nothing _ k , _) = just (Tkk (qualif-kind Γ k))
... | just (term-decl t , _) = just (Tkt (qualif-type Γ t))
... | just (term-def nothing _ t , _) = just (Tkt (qualif-type Γ t))
... | _ with trie-lookup q v
... | just (v' , as) = env-lookup-tk-var Γ v' as
... | _ = nothing

env-lookup-kind-var-qdef : ctxt → var → args → maybe (params × kind)
env-lookup-kind-var-qdef Γ@(mk-ctxt _ _ i _) v as with trie-lookup i v
... | just (kind-def ps1 ps2 k , _) = just (inst-params Γ ps1 as ps2 , inst-kind Γ ps1 as k)
... | _ = nothing

ctxt-lookup-kind-var-qdef : ctxt → var → maybe (params × kind)
ctxt-lookup-kind-var-qdef Γ@(mk-ctxt (_ , _ , _ , q) _ i _) v with trie-lookup q v
... | just (v' , as) = env-lookup-kind-var-qdef Γ v' as
... | _ = nothing

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def (mk-ctxt _ _ i _) v with trie-lookup i v
... | just (term-def nothing t _ , _) = just t
... | just (term-udef nothing t , _) = just t
... | just (term-def (just ps) t _ , _) = just (abs-expand-term ps t)
... | just (term-udef (just ps) t , _) = just (abs-expand-term ps t)
... | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def (mk-ctxt _ _ i _) v with trie-lookup i v
... | just (type-def nothing t _ , _) = just t
... | just (type-def (just ps) t _ , _) = just (abs-expand-type ps t)
... | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe (params × kind)
ctxt-lookup-kind-var-def (mk-ctxt _ _ i _) x with trie-lookup i x
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

ctxt-set-current-file : ctxt → string → string → ctxt
ctxt-set-current-file (mk-ctxt _ syms i symb-occs) fn mn = mk-ctxt (fn , mn , ParamsNil , empty-trie) syms i symb-occs

ctxt-set-current-mod : ctxt → mod-info → ctxt
ctxt-set-current-mod (mk-ctxt _ syms i symb-occs) m = mk-ctxt m syms i symb-occs

-- TODO I think this should trie-remove the List occurrence of the filename lookup of syms
ctxt-clear-symbol : ctxt → string → ctxt
ctxt-clear-symbol (mk-ctxt (fn , mn , pms , q) syms i symb-occs) x = mk-ctxt (fn , mn , pms , (trie-remove q x)) (trie-remove syms x) (trie-remove i x) symb-occs

ctxt-clear-symbols : ctxt → 𝕃 string → ctxt
ctxt-clear-symbols Γ [] = Γ
ctxt-clear-symbols Γ (v :: vs) = ctxt-clear-symbols (ctxt-clear-symbol Γ v) vs

ctxt-clear-symbols-of-file : ctxt → (filename : string) → ctxt
ctxt-clear-symbols-of-file (mk-ctxt f syms i symb-occs) fn = mk-ctxt f (trie-insert syms fn (fst p , []))
                                                                  (hremove i (fst p) (snd p))
                                                                  symb-occs
  where
  p = trie-lookup𝕃2 syms fn
  hremove : ∀ {A : Set} → trie A → var → 𝕃 string → trie A
  hremove i mn [] = i
  hremove i mn (x :: xs) = hremove (trie-remove i (mn # x)) mn xs

ctxt-initiate-file : ctxt → (filename modname : string) → ctxt
ctxt-initiate-file Γ fn mn = ctxt-set-current-file (ctxt-clear-symbols-of-file Γ fn) fn mn

ctxt-get-current-filename : ctxt → string
ctxt-get-current-filename (mk-ctxt (fn , _) _ _ _) = fn

ctxt-get-current-mod : ctxt → mod-info
ctxt-get-current-mod (mk-ctxt m _ _ _) = m

ctxt-get-symbol-occurrences : ctxt → trie (𝕃 (var × posinfo × string))
ctxt-get-symbol-occurrences (mk-ctxt _ _ _ symb-occs) = symb-occs

ctxt-set-symbol-occurrences : ctxt → trie (𝕃 (var × posinfo × string)) → ctxt
ctxt-set-symbol-occurrences (mk-ctxt fn syms i symb-occs) new-symb-occs = mk-ctxt fn syms i new-symb-occs

unqual : ctxt → var → string
unqual (mk-ctxt (_ , _ , _ , q) _ _ _ ) v = unqual-all q v

