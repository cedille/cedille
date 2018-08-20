import cedille-options
module elaboration (options : cedille-options.options) where

open import lib

options' = record options
  {during-elaboration = tt;
   erase-types = ff;
   show-qualified-vars = ff}

open import general-util
open import monad-instances
open import cedille-types
open import classify options' {id}
open import ctxt
open import constants
open import conversion
open import is-free
open import meta-vars options' {id}
open import spans options {IO}
open import subst
open import syntax-util
open import toplevel-state options {IO}
open import to-string options'
open import rename
open import rewriting
import spans options' {id} as id-spans

private

  foldl : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (A → B → B) → B → 𝕃 A → B
  foldl f b [] = b
  foldl f b (a :: as) = foldl f (f a b) as

  ctxt-var-decl' = ctxt-var-decl posinfo-gen
  
  uncurry' : ∀ {A B C D : Set} → (A → B → C → D) → (A × B × C) → D
  uncurry' f (a , b , c) = f a b c

  uncurry'' : ∀ {A B C D E : Set} → (A → B → C → D → E) → (A × B × C × D) → E
  uncurry'' f (a , b , c , d) = f a b c d

  ctxt-term-decl' : posinfo → var → type → ctxt → ctxt
  ctxt-term-decl' pi x T (mk-ctxt (fn , mn , ps , q) ss is os) =
    mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
      (trie-insert is x (term-decl T , fn , pi)) os

  ctxt-type-decl' : posinfo → var → kind → ctxt → ctxt
  ctxt-type-decl' pi x k (mk-ctxt (fn , mn , ps , q) ss is os) =
    mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
      (trie-insert is x (type-decl k , fn , pi)) os

  ctxt-tk-decl' : posinfo → var → tk → ctxt → ctxt
  ctxt-tk-decl' pi x (Tkt T) = ctxt-term-decl' pi x T
  ctxt-tk-decl' pi x (Tkk k) = ctxt-type-decl' pi x k

  ctxt-param-decl : var → var → tk → ctxt → ctxt
  ctxt-param-decl x x' atk Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) =
    let d = case atk of λ {(Tkt T) → term-decl T; (Tkk k) → type-decl k} in
    mk-ctxt
    (fn , mn , ps , trie-insert q x (mn # x , ArgsNil)) ss
    (trie-insert is x' (d , fn , posinfo-gen)) os

  ctxt-term-def' : var → var → term → type → opacity → ctxt → ctxt
  ctxt-term-def' x x' t T op Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) = mk-ctxt
    (fn , mn , ps , qualif-insert-params q (mn # x) x ps) ss
    (trie-insert is x' (term-def (just ps) op (hnf Γ unfold-head t tt) T , fn , x)) os

  ctxt-type-def' : var → var → type → kind → opacity → ctxt → ctxt
  ctxt-type-def' x x' T k op Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) = mk-ctxt
    (fn , mn , ps , qualif-insert-params q (mn # x) x ps) ss
    (trie-insert is x' (type-def (just ps) op (hnf Γ (unfolding-elab unfold-head) T tt) k , fn , x)) os

  ctxt-let-term-def : posinfo → var → term → type → ctxt → ctxt
  ctxt-let-term-def pi x t T (mk-ctxt (fn , mn , ps , q) ss is os) =
    mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
      (trie-insert is x (term-def nothing OpacTrans t T , fn , pi)) os
  
  ctxt-let-type-def : posinfo → var → type → kind → ctxt → ctxt
  ctxt-let-type-def pi x T k (mk-ctxt (fn , mn , ps , q) ss is os) =
    mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
      (trie-insert is x (type-def nothing OpacTrans T k , fn , pi)) os
  
  ctxt-kind-def' : var → var → params → kind → ctxt → ctxt
  ctxt-kind-def' x x' ps2 k Γ @ (mk-ctxt (fn , mn , ps1 , q) ss is os) = mk-ctxt
    (fn , mn , ps1 , qualif-insert-params q (mn # x) x ps1) ss
    (trie-insert is x' (kind-def ps1 (h Γ ps2) k' , fn , posinfo-gen)) os
    where
      k' = hnf Γ unfold-head k tt
      h : ctxt → params → params
      h Γ (ParamsCons (Decl pi pi' me x atk pi'') ps) =
        ParamsCons (Decl pi pi' me (pi' % x) (qualif-tk Γ atk) pi'') (h (ctxt-tk-decl pi' localScope x atk Γ) ps)
      h _ ps = ps

  ctxt-lookup-term-var' : ctxt → var → maybe type
  ctxt-lookup-term-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) x =
    env-lookup Γ x ≫=maybe λ where
      (term-decl T , _) → just T
      (term-def ps _ _ T , _ , x') →
        let ps = maybe-else ParamsNil id ps in
        just (abs-expand-type ps T)
      _ → nothing
  
  -- TODO: Could there be parameter/argument clashes if the same parameter variable is defined multiple times?
  -- TODO: Could variables be parameter-expanded multiple times?
  ctxt-lookup-type-var' : ctxt → var → maybe kind
  ctxt-lookup-type-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) x =
    env-lookup Γ x ≫=maybe λ where
      (type-decl k , _) → just k
      (type-def ps _ _ k , _ , x') →
        let ps = maybe-else ParamsNil id ps in
        just (abs-expand-kind ps k)
      _ → nothing
  
  subst : ∀ {ed ed' : exprd} → ctxt → ⟦ ed' ⟧ → var → ⟦ ed ⟧ → ⟦ ed ⟧
  subst{TERM} = subst-term
  subst{TYPE} = subst-type
  subst{KIND} = subst-kind
  subst Γ _ _ x = x

  renamectxt-single : var → var → renamectxt
  renamectxt-single = renamectxt-insert empty-renamectxt

  rename-var : ∀ {ed : exprd} → ctxt → var → var → ⟦ ed ⟧ → ⟦ ed ⟧
  rename-var {TERM} Γ x x' = substh-term {LIFTINGTYPE} Γ (renamectxt-single x x') empty-trie
  rename-var {TYPE} Γ x x' = substh-type {LIFTINGTYPE} Γ (renamectxt-single x x') empty-trie
  rename-var {KIND} Γ x x' = substh-kind {LIFTINGTYPE} Γ (renamectxt-single x x') empty-trie
  rename-var Γ x x' = id
  
  subst-qualif : ∀ {ed : exprd} → ctxt → renamectxt → ⟦ ed ⟧ → ⟦ ed ⟧
  subst-qualif{TERM} Γ ρ = substh-term {TERM} Γ ρ empty-trie ∘ qualif-term Γ
  subst-qualif{TYPE} Γ ρ = substh-type {TYPE} Γ ρ empty-trie ∘ qualif-type Γ
  subst-qualif{KIND} Γ ρ = substh-kind {KIND} Γ ρ empty-trie ∘ qualif-kind Γ
  subst-qualif Γ ρ = id

  rename-validify : string → string
  rename-validify = 𝕃char-to-string ∘ (h ∘ string-to-𝕃char) where
    validify-char : char → 𝕃 char
    validify-char c with
      (c =char 'a')  ||
      (c =char 'z')  ||
      (c =char 'A')  ||
      (c =char 'Z')  ||
      (c =char '\'') ||
      (c =char '-')  ||
      (c =char '_')  ||
      is-digit c     ||
      (('a' <char c) && (c <char 'z')) ||
      (('A' <char c) && (c <char 'Z'))
    ...| tt = [ c ]
    ...| ff = 'Z' :: string-to-𝕃char (ℕ-to-string (toNat c)) ++ [ 'Z' ]
    h : 𝕃 char → 𝕃 char
    h [] = []
    h (c :: cs) = validify-char c ++ h cs

  -- Returns a fresh variable name by adding primes and replacing invalid characters
  fresh-var' : string → (string → 𝔹) → renamectxt → string
  fresh-var' = fresh-var ∘ rename-validify

  rename-new_from_for_ : ∀ {X : Set} → var → ctxt → (var → X) → X
  rename-new "_" from Γ for f = f (fresh-var' "x" (ctxt-binds-var Γ) empty-renamectxt)
  rename-new x from Γ for f = f (fresh-var' x (ctxt-binds-var Γ) empty-renamectxt)
  
  rename_from_for_ : ∀ {X : Set} → var → ctxt → (var → X) → X
  rename "_" from Γ for f = f "_"
  rename x from Γ for f = f (fresh-var' x (ctxt-binds-var Γ) empty-renamectxt)
  
  fresh-id-term : ctxt → term
  fresh-id-term Γ = rename "x" from Γ for λ x → mlam x (mvar x)

  get-renaming : renamectxt → var → var → var × renamectxt
  get-renaming ρ xₒ x = let x' = fresh-var' x (renamectxt-in-range ρ) ρ in x' , renamectxt-insert ρ xₒ x'

  rename_-_from_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
  rename xₒ - "_" from ρ for f = f "_" ρ
  rename xₒ - x from ρ for f = uncurry f (get-renaming ρ xₒ x)

  rename_-_lookup_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
  rename xₒ - x lookup ρ for f with renamectxt-lookup ρ xₒ
  ...| nothing = rename xₒ - x from ρ for f
  ...| just x' = f x' ρ
  
  qualif-new-var : ctxt → var → var
  qualif-new-var Γ x = ctxt-get-current-modname Γ # x

  mbeta : term → term → term
  mrho : term → var → type → term → term
  mtpeq : term → term → type
  mbeta t t' = Beta posinfo-gen (SomeTerm t posinfo-gen) (SomeTerm t' posinfo-gen)
  mrho t x T t' = Rho posinfo-gen RhoPlain NoNums t (Guide posinfo-gen x T) t'
  mtpeq t1 t2 = TpEq posinfo-gen t1 t2 posinfo-gen

  subst-args-params : ctxt → args → params → kind → kind
  subst-args-params Γ (ArgsCons (TermArg _ t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = subst-args-params Γ ys ps (subst-kind Γ t x k)
  subst-args-params Γ (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = subst-args-params Γ ys ps (subst-kind Γ t x k)
  subst-args-params Γ ys ps k = k

  params-append : params → params → params
  params-append ParamsNil ps = ps
  params-append (ParamsCons p ps) ps' = ParamsCons p (params-append ps ps')
  
  drop-meta-var : meta-vars → meta-vars
  drop-meta-var Xs = record Xs {order = tail (meta-vars.order Xs)}

  drop-meta-vars : meta-vars → ℕ → meta-vars
  drop-meta-vars Xs zero = Xs
  drop-meta-vars Xs (suc n) = drop-meta-vars (drop-meta-var Xs) n

  file-to-string : start → strM
  cmds-to-string : cmds → strM → strM
  cmd-to-string : cmd → strM → strM  

  ie-set-span-ast : include-elt → ctxt → start → include-elt
  ie-set-span-ast ie Γ ast = record ie
    {ss = inj₁ (regular-spans nothing [ mk-span "" "" "" [ "" , strRun Γ (file-to-string ast) , [] ] nothing ])}

  ie-get-span-ast : include-elt → maybe rope
  ie-get-span-ast ie = case include-elt.ss ie of λ where
    (inj₁ (regular-spans nothing (mk-span "" "" "" (("" , r , []) :: []) nothing :: []))) → just r
    _ → nothing

  file-to-string (File _ is _ _ mn ps cs _) =
     cmds-to-string (imps-to-cmds is)
    (strAdd "module " ≫str
     strAdd mn ≫str
     strAdd " " ≫str
     params-to-string' globalScope
    (strAdd "." ≫str strAdd "\n" ≫str
     cmds-to-string cs strEmpty) ps)
  
  cmds-to-string CmdsStart f = f
  cmds-to-string (CmdsNext c cs) f =
     strAdd "\n" ≫str
     cmd-to-string c
    (strAdd "\n" ≫str
     cmds-to-string cs f)
    
  cmd-to-string (DefTermOrType op (DefTerm pi x mcT t) _) f =
    strM-Γ λ Γ →
    let ps = ctxt-get-current-params Γ in
    strAdd x ≫str
    maybeCheckType-to-string (case mcT of λ where
       NoType → NoType
       (SomeType T) → SomeType (abs-expand-type ps T)) ≫str
    strAdd " = " ≫str
    to-stringh (lam-expand-term ps t) ≫str
    strAdd " ." ≫str
    strΓ' globalScope tt x pi f
  cmd-to-string (DefTermOrType op (DefType pi x k T) _) f =
    strM-Γ λ Γ →
    let ps = ctxt-get-current-params Γ in
    strAdd x ≫str
    strAdd " ◂ " ≫str
    to-stringh (abs-expand-kind ps k) ≫str
    strAdd " = " ≫str
    to-stringh (lam-expand-type ps T) ≫str
    strAdd " ." ≫str
    strΓ' globalScope tt x pi f
  cmd-to-string (DefKind pi x ps k _) f =
    strM-Γ λ Γ →
    let ps' = ctxt-get-current-params Γ in
    strAdd x ≫str
    params-to-string (params-append ps' ps) ≫str
    strAdd " = " ≫str
    to-stringh k ≫str
    strAdd " ." ≫str
    strΓ' globalScope tt x pi f
  cmd-to-string (ImportCmd (Import _ op _ fn oa as _)) f =
    strAdd "import " ≫str
    strAdd (optPublic-to-string op) ≫str
    strAdd fn ≫str
    optAs-to-string oa ≫str
    args-to-string as ≫str
    strAdd " ." ≫str
    f

{-# TERMINATING #-}
elab-check-term : ctxt → term → type → maybe term
elab-synth-term : ctxt → term → maybe (term × type)
elab-pure-term : ctxt → term → maybe term
elab-type : ctxt → type → maybe (type × kind)
elab-pure-type : ctxt → type → maybe type
elab-kind : ctxt → kind → maybe kind
elab-pure-kind : ctxt → kind → maybe kind
elab-tk : ctxt → tk → maybe tk
elab-pure-tk : ctxt → tk → maybe tk

elab-typeh : ctxt → type → 𝔹 → maybe (type × kind)
elab-kindh : ctxt → kind → 𝔹 → maybe kind
elab-tkh : ctxt → tk → 𝔹 → maybe tk
elab-type-arrow : type → type
elab-kind-arrow : kind → kind
elab-tk-arrow : tk → tk
elab-hnf-type : ctxt → type → 𝔹 → maybe type
elab-hnf-kind : ctxt → kind → 𝔹 → maybe kind
elab-hnf-tk : ctxt → tk → 𝔹 → maybe tk
elab-app-term : ctxt → term → maybe ((meta-vars → maybe term) × type × meta-vars)

elab-type Γ T = elab-typeh Γ T tt
elab-kind Γ k = elab-kindh Γ k tt
elab-tk Γ atk = elab-tkh Γ atk tt
elab-pure-type Γ T = maybe-map fst (elab-typeh Γ T ff)
elab-pure-kind Γ k = elab-kindh Γ k ff
elab-pure-tk Γ atk = elab-tkh Γ atk ff

elab-type-arrow (Abs pi b pi' x atk T) = Abs pi b pi' x (elab-tk-arrow atk) (elab-type-arrow T)
elab-type-arrow (Iota pi pi' x T T') = Iota pi pi' x (elab-type-arrow T) (elab-type-arrow T')
elab-type-arrow (TpApp T T') = TpApp (elab-type-arrow T) (elab-type-arrow T')
elab-type-arrow (TpAppt T t) = TpAppt (elab-type-arrow T) t
elab-type-arrow (TpArrow T a T') = Abs posinfo-gen a posinfo-gen "_" (Tkt (elab-type-arrow T)) (elab-type-arrow T')
elab-type-arrow (TpEq pi t t' pi') = TpEq pi (erase-term t) (erase-term t') pi'
elab-type-arrow (TpLambda pi pi' x atk T) = TpLambda pi pi' x (elab-tk-arrow atk) (elab-type-arrow T)
elab-type-arrow (TpParens pi T pi') = elab-type-arrow T
elab-type-arrow T = T

elab-kind-arrow (KndArrow k k') = KndPi posinfo-gen posinfo-gen "_" (Tkk (elab-kind-arrow k)) (elab-kind-arrow k')
elab-kind-arrow (KndParens pi k pi') = elab-kind-arrow k
elab-kind-arrow (KndPi pi pi' x atk k) = KndPi pi pi' x (elab-tk-arrow atk) (elab-kind-arrow k)
elab-kind-arrow (KndTpArrow T k) = KndPi posinfo-gen posinfo-gen "_" (Tkt (elab-type-arrow T)) (elab-kind-arrow k)
elab-kind-arrow k = k

elab-tk-arrow (Tkt T) = Tkt (elab-type-arrow T)
elab-tk-arrow (Tkk k) = Tkk (elab-kind-arrow k)

elab-hnf-type Γ T b = just (elab-type-arrow (substh-type {TYPE} Γ empty-renamectxt empty-trie (hnf Γ (unfolding-set-erased unfold-head (~ b)) T tt)))
elab-hnf-kind Γ k b = just (elab-kind-arrow (substh-kind {KIND} Γ empty-renamectxt empty-trie (hnf Γ (unfolding-set-erased unfold-head (~ b)) k tt)))
elab-hnf-tk Γ (Tkt T) b = elab-hnf-type Γ T b ≫=maybe (just ∘ Tkt)
elab-hnf-tk Γ (Tkk k) b = elab-hnf-kind Γ k b ≫=maybe (just ∘ Tkk)


elab-check-term Γ (App t me t') T =
  elab-app-term Γ (App t me t') ≫=maybe uncurry' λ tf T Xs → tf Xs
elab-check-term Γ (AppTp t T) T' =
  elab-app-term Γ (AppTp t T) ≫=maybe uncurry' λ tf T Xs → tf Xs
elab-check-term Γ (Beta pi ot ot') T =
  let ot'' = case ot' of λ where NoTerm → just (fresh-id-term Γ); (SomeTerm t _) → elab-pure-term Γ (erase-term t) in
  case ot of λ where
    NoTerm → elab-hnf-type Γ T tt ≫=maybe λ where
      (TpEq _ t₁ t₂ _) → ot'' ≫=maybe (just ∘ mbeta t₁)
      _ → nothing
    (SomeTerm t _) →
      elab-pure-term Γ (erase-term t) ≫=maybe λ t →
      ot'' ≫=maybe (just ∘ mbeta t)
elab-check-term Γ (Chi pi mT t) T = case mT of λ where
  NoType → maybe-map fst (elab-synth-term Γ t)
  (SomeType T') →
    elab-pure-type Γ (erase-type T') ≫=maybe λ T' →
    let id = fresh-id-term Γ in
    elab-check-term Γ t T' ≫=maybe
    (just ∘ mrho (mbeta id id) "_" T')
elab-check-term Γ (Delta pi mT t) T =
  elab-pure-type Γ (erase-type T) ≫=maybe λ T →
  elab-synth-term Γ t ≫=maybe uncurry λ where
    t (TpEq _ t1 t2 _) →
      rename "x" from Γ for λ x →
      rename "y" from Γ for λ y →
      rename "z" from Γ for λ z →
      let ρ = renamectxt-insert (renamectxt-insert (renamectxt-insert empty-renamectxt x x) y y) z z
          tt-term = mlam x (mlam y (mvar x))
          ff-term = mlam x (mlam y (mvar y)) in
      if conv-term Γ t1 tt-term && conv-term Γ t2 ff-term
        then just (Delta posinfo-gen (SomeType T) t)
        else
          delta-contra (hnf Γ unfold-head t1 tt) (hnf Γ unfold-head t2 tt) ≫=maybe λ f →
          let f = substh-term {TERM} Γ ρ empty-trie f in
          elab-pure-term Γ (erase-term t) ≫=maybe λ pt →
          just (Delta posinfo-gen (SomeType T)
            (mrho t z (mtpeq (mapp f t1) (mapp f (mvar z))) (mbeta tt-term pt)))
    t T → nothing
elab-check-term Γ (Epsilon pi lr mm t) T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (TpEq _ t₁ t₂ _) → elab-check-term Γ (Chi posinfo-gen
      (SomeType (check-term-update-eq Γ lr mm posinfo-gen t₁ t₂ posinfo-gen)) t) T
    _ → nothing
elab-check-term Γ (Hole pi) T = nothing
elab-check-term Γ (IotaPair pi t t' og pi') T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (Iota _ pi x T' T'') →
      elab-check-term Γ t T' ≫=maybe λ t →
      elab-check-term Γ t' (subst Γ t x T'') ≫=maybe λ t' →
      rename x from Γ for λ x' →
      just (IotaPair posinfo-gen t t' (Guide posinfo-gen x' T'') posinfo-gen)
    _ → nothing
elab-check-term Γ (IotaProj t n pi) T =
  elab-synth-term Γ t ≫=maybe uncurry λ t T' →
  just (IotaProj t n posinfo-gen)
elab-check-term Γ (Lam pi l pi' x oc t) T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (Abs _ b pi'' x' atk T') →
      rename (if x =string "_" && is-free-in tt x' T' then x' else x) from Γ for λ x'' →
      elab-hnf-tk Γ atk tt ≫=maybe λ atk →
      elab-check-term (ctxt-tk-decl' pi' x'' atk Γ) (rename-var Γ x x'' t)
        (rename-var Γ x' x'' T') ≫=maybe λ t →
      just (Lam posinfo-gen l posinfo-gen x'' (SomeClass atk) t)
    _ → nothing
elab-check-term Γ (Let pi d t) T =
  case d of λ where
  (DefTerm pi' x NoType t') →
    rename x from Γ for λ x' →
    elab-synth-term Γ t' ≫=maybe uncurry λ t' T' →
    elab-check-term (ctxt-let-term-def pi' x' t' T' Γ) (rename-var Γ x x' t) T ≫=maybe λ t →
    just (Let posinfo-gen (DefTerm posinfo-gen x' NoType t') t)
  (DefTerm pi' x (SomeType T') t') →
    rename x from Γ for λ x' →
    elab-type Γ T' ≫=maybe uncurry λ T' k →
    elab-check-term Γ t' T' ≫=maybe λ t' →
    elab-check-term (ctxt-let-term-def pi' x' t' T' Γ) (rename-var Γ x x' t) T ≫=maybe λ t →
    just (Let posinfo-gen (DefTerm posinfo-gen x' NoType t') t)
  (DefType pi' x k T') →
    rename x from Γ for λ x' →
    elab-type Γ T' ≫=maybe uncurry λ T' k' →
    elab-check-term (ctxt-let-type-def pi' x' T' k' Γ) (rename-var Γ x x' t) T ≫=maybe λ t →
    just (Let posinfo-gen (DefType posinfo-gen x' k' T') t)
elab-check-term Γ (Open pi x t) T =
  ctxt-clarify-def Γ x ≫=maybe uncurry λ _ Γ →
  elab-check-term Γ t T
elab-check-term Γ (Parens pi t pi') T = elab-check-term Γ t T
elab-check-term Γ (Phi pi t t₁ t₂ pi') T =
  elab-pure-term Γ (erase-term t₁) ≫=maybe λ t₁' →
  elab-pure-term Γ (erase-term t₂) ≫=maybe λ t₂ →
  elab-check-term Γ t₁ T ≫=maybe λ t₁ →
  elab-check-term Γ t (mtpeq t₁' t₂) ≫=maybe λ t →
  just (Phi posinfo-gen t t₁ t₂ posinfo-gen)
elab-check-term Γ (Rho pi op on t og t') T =
  elab-synth-term Γ t ≫=maybe uncurry λ t T' →
  elab-hnf-type Γ (erase-type T') ff ≫=maybe λ where
    (TpEq _ t₁ t₂ _) → case og of λ where
      NoGuide →
        elab-hnf-type Γ T tt ≫=maybe λ T →
        rename "x" from Γ for λ x →
        let ns = fst (optNums-to-stringset on)
            Γ' = ctxt-var-decl posinfo-gen x Γ
            rT = fst (rewrite-type T Γ' (is-rho-plus op) ns t t₁ x 0)
            rT' = post-rewrite Γ x t t₂ rT in
        elab-hnf-type Γ rT' tt ≫=maybe λ rT' →
        elab-check-term Γ t' rT' ≫=maybe
        (just ∘ mrho (Sigma posinfo-gen t) x (erase-type rT))
      (Guide pi' x T') →
        let Γ' = ctxt-var-decl pi' x Γ in
        elab-pure-type Γ' (erase-type T') ≫=maybe λ T' →
        elab-check-term Γ t' (post-rewrite Γ' x t t₂ (rewrite-at Γ' x t tt T T')) ≫=maybe
        (just ∘ mrho t x T')
    _ → nothing
elab-check-term Γ (Sigma pi t) T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (TpEq _ t₁ t₂ _) →
      elab-check-term Γ t (mtpeq t₂ t₁) ≫=maybe λ t →
      just (Sigma posinfo-gen t)
    _ → nothing
elab-check-term Γ (Theta pi θ t ts) T =
  elab-synth-term Γ t ≫=maybe uncurry λ t T' →
  let x = case hnf Γ unfold-head t tt of λ {(Var _ x) → x; _ → "_"} in
  rename x from Γ for λ x' →
  motive x x' T T' θ ≫=maybe λ mtv →
  elab-check-term Γ (lterms-to-term θ (AppTp t mtv) ts) T where
  wrap-var : var → type → maybe type
  wrap-var x T =
    rename x from Γ for λ x' →
    env-lookup Γ x ≫=maybe λ where
      (term-decl T' , loc) → just (mtplam x' (Tkt T') (rename-var Γ x x' T))
      (type-decl k , loc) → just (mtplam x' (Tkk k) (rename-var Γ x x' T))
      (term-def ps _ _ T' , loc) → just (mtplam x' (Tkt T') (rename-var Γ x x' T))
      (type-def ps _ _ k , loc) → just (mtplam x' (Tkk k) (rename-var Γ x x' T))
      _ → nothing
  wrap-vars : vars → type → maybe type
  wrap-vars (VarsStart x) T = wrap-var x  T
  wrap-vars (VarsNext x xs) T = wrap-vars xs T ≫=maybe wrap-var x

  motive : var → var → type → type → theta → maybe type
  motive x x' T T' Abstract = just (mtplam x' (Tkt T') (rename-var Γ x x' T))
  motive x x' T T' AbstractEq = just (mtplam x' (Tkt T') (TpArrow (mtpeq t (mvar x')) Erased (rename-var Γ x x' T)))
  motive x x' T T' (AbstractVars vs) = wrap-vars vs T
elab-check-term Γ (Var pi x) T = just (mvar x)

elab-synth-term Γ (App t me t') =
  elab-app-term Γ (App t me t') ≫=maybe λ where
    (tf , T , Xs) → tf Xs ≫=maybe λ t →
      elab-hnf-type Γ (substh-type Γ empty-renamectxt (meta-vars-get-sub Xs) T) tt ≫=maybe λ T →
      just (t , T)
elab-synth-term Γ (AppTp t T) =
  elab-app-term Γ (AppTp t T) ≫=maybe λ where
    (tf , T , Xs) → tf Xs ≫=maybe λ t →
      elab-hnf-type Γ (substh-type Γ empty-renamectxt (meta-vars-get-sub Xs) T) tt ≫=maybe λ T →
      just (t , T)
elab-synth-term Γ (Beta pi ot ot') =
  let ot'' = case ot' of λ where NoTerm → just (fresh-id-term Γ); (SomeTerm t _) → elab-pure-term Γ (erase-term t) in
  case ot of λ where
    (SomeTerm t _) →
      elab-pure-term Γ (erase-term t) ≫=maybe λ t →
      ot'' ≫=maybe λ t' →
      just (mbeta t t' , mtpeq t t)
    NoTerm → nothing
elab-synth-term Γ (Chi pi mT t) = case mT of λ where
  NoType → elab-synth-term Γ t
  (SomeType T') →
    let id = fresh-id-term Γ in
    elab-pure-type Γ (erase-type T') ≫=maybe λ T' →
    elab-check-term Γ t T' ≫=maybe λ t →
    just (mrho (mbeta id id) "_" T' t , T')
elab-synth-term Γ (Delta pi mT t) = (case mT of λ where
  NoType → just compileFailType
  (SomeType T) → elab-pure-type Γ (erase-type T)) ≫=maybe λ T →
  elab-synth-term Γ t ≫=maybe uncurry λ where
    t (TpEq _ t1 t2 _) →
      elab-pure-term Γ (erase-term t) ≫=maybe λ pt →
      rename "x" from Γ for λ x →
      rename "y" from Γ for λ y →
      rename "z" from Γ for λ z →
      let ρ = renamectxt-insert (renamectxt-insert (renamectxt-insert empty-renamectxt x x) y y) z z
          tt-term = mlam x (mlam y (mvar x))
          ff-term = mlam x (mlam y (mvar y)) in
      if conv-term Γ t1 tt-term && conv-term Γ t2 ff-term
        then just (Delta posinfo-gen (SomeType T) t , T)
        else
          delta-contra (hnf Γ unfold-head t1 tt) (hnf Γ unfold-head t2 tt) ≫=maybe λ f →
          let f = substh-term {TERM} Γ ρ empty-trie f in
          just (Delta posinfo-gen (SomeType T)
            (mrho t z (mtpeq (mapp f t1) (mapp f (mvar z))) (mbeta tt-term pt)) , T)
    t T → nothing
elab-synth-term Γ (Epsilon pi lr mm t) =
  elab-synth-term Γ t ≫=maybe uncurry λ where
    t (TpEq _ t₁ t₂ _) →
      let id = fresh-id-term Γ
          T = check-term-update-eq Γ lr mm posinfo-gen t₁ t₂ posinfo-gen in
      elab-pure-type Γ T ≫=maybe λ T →
      just (mrho (mbeta id id) "_" T t , T)
    _ _ → nothing
elab-synth-term Γ (Hole pi) = nothing
elab-synth-term Γ (IotaPair pi t₁ t₂ og pi') = case og of λ where
  NoGuide → nothing
  (Guide pi'' x T₂) →
    rename x from Γ for λ x' →
    elab-type (ctxt-var-decl pi'' x' Γ) (rename-var Γ x x' T₂) ≫=maybe uncurry λ T₂ k₂ →
    elab-synth-term Γ t₁ ≫=maybe uncurry λ t₁ T₁ →
    elab-check-term Γ t₂ (subst Γ t₁ x' T₂) ≫=maybe λ t₂ →
    just (IotaPair posinfo-gen t₁ t₂ (Guide posinfo-gen x' T₂) posinfo-gen ,
          Iota posinfo-gen posinfo-gen x' T₁ T₂)
elab-synth-term Γ (IotaProj t n pi) =
  elab-synth-term Γ t ≫=maybe uncurry λ where
    t (Iota _ pi' x T₁ T₂) →
      case n of λ where
        "1" → elab-hnf-type Γ T₁ tt ≫=maybe λ T₁ →
              just (IotaProj t n posinfo-gen , T₁)
        "2" → elab-hnf-type Γ (subst Γ (IotaProj t "1" posinfo-gen) x T₂) tt ≫=maybe λ T₂ →
              just (IotaProj t n posinfo-gen , T₂)
        _ → nothing
    _ _ → nothing
elab-synth-term Γ (Lam pi l pi' x oc t) = (case (l , oc) of λ where
  (Erased , SomeClass atk) → elab-tk Γ atk
  (NotErased , SomeClass (Tkt T)) → elab-tk Γ (Tkt T)
  _ → nothing) ≫=maybe λ atk →
  rename x from Γ for λ x' →
  elab-synth-term (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' t) ≫=maybe uncurry λ t T →
    just (Lam posinfo-gen l posinfo-gen x' (SomeClass atk) t , Abs posinfo-gen l posinfo-gen x' atk T)
elab-synth-term Γ (Let pi d t) = case d of λ where
  (DefTerm pi' x NoType t') →
    rename x from Γ for λ x' →
    elab-synth-term Γ t' ≫=maybe uncurry λ t' T' →
    elab-synth-term (ctxt-let-term-def pi' x' t' T' Γ) (rename-var Γ x x' t) ≫=maybe uncurry λ t T →
    just (Let posinfo-gen (DefTerm posinfo-gen x' NoType t') t , subst Γ t' x' T)
  (DefTerm pi' x (SomeType T') t') →
    rename x from Γ for λ x' →
    elab-type Γ T' ≫=maybe uncurry λ T' k →
    elab-check-term Γ t' T' ≫=maybe λ t' →
    elab-synth-term (ctxt-let-term-def pi' x' t' T' Γ) (rename-var Γ x x' t) ≫=maybe uncurry λ t T →
    just (Let posinfo-gen (DefTerm posinfo-gen x' NoType t') t , subst Γ t' x' T)
  (DefType pi' x k T') →
    rename x from Γ for λ x' →
    elab-type Γ T' ≫=maybe uncurry λ T' k' →
    elab-synth-term (ctxt-let-type-def pi' x' T' k' Γ) (rename-var Γ x x' t) ≫=maybe uncurry λ t T →
    just (Let posinfo-gen (DefType pi' x' k' T') t , subst Γ T' x' T)
elab-synth-term Γ (Open pi x t) =
  ctxt-clarify-def Γ x ≫=maybe uncurry λ _ Γ →
  elab-synth-term Γ t
elab-synth-term Γ (Parens pi t pi') = elab-synth-term Γ t
elab-synth-term Γ (Phi pi t t₁ t₂ pi') =
  elab-pure-term Γ (erase-term t₁) ≫=maybe λ t₁' →
  elab-pure-term Γ (erase-term t₂) ≫=maybe λ t₂ →
  elab-synth-term Γ t₁ ≫=maybe uncurry λ t₁ T →
  elab-check-term Γ t (mtpeq t₁' t₂) ≫=maybe λ t →
  just (Phi posinfo-gen t t₁ t₂ posinfo-gen , T)
elab-synth-term Γ (Rho pi op on t og t') =
  elab-synth-term Γ t ≫=maybe uncurry λ t T →
  elab-synth-term Γ t' ≫=maybe uncurry λ t' T' →
  elab-hnf-type Γ (erase-type T) ff ≫=maybe λ where
    (TpEq _ t₁ t₂ _) → case og of λ where
      NoGuide →
        rename "x" from Γ for λ x →
        let ns = fst (optNums-to-stringset on)
            Γ' = ctxt-var-decl posinfo-gen x Γ
            rT = fst (rewrite-type T' Γ' (is-rho-plus op) ns t t₁ x 0)
            rT' = post-rewrite Γ' x t t₂ rT in
        elab-hnf-type Γ rT' tt ≫=maybe λ rT' →
        just (mrho t x (erase-type rT) t' , rT')
      (Guide pi' x T'') →
        let Γ' = ctxt-var-decl pi' x Γ in
        elab-pure-type Γ' (erase-type T') ≫=maybe λ T'' →
        just (mrho t x T' t' , post-rewrite Γ' x t t₂ (rewrite-at Γ' x t tt T' T''))
    _ → nothing
elab-synth-term Γ (Sigma pi t) =
  elab-synth-term Γ t ≫=maybe uncurry λ where
    t (TpEq _ t₁ t₂ _) → just (Sigma posinfo-gen t , mtpeq t₂ t₁)
    _ _ → nothing
elab-synth-term Γ (Theta pi θ t ts) = nothing
elab-synth-term Γ (Var pi x) =
  ctxt-lookup-term-var' Γ x ≫=maybe λ T →
  elab-hnf-type Γ T tt ≫=maybe λ T →
  just (mvar x , T)

elab-typeh Γ (Abs pi b pi' x atk T) b' =
  elab-tkh Γ atk b' ≫=maybe λ atk →
  rename x from Γ for λ x' →
  elab-typeh (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' T) b' ≫=maybe uncurry λ T k →
  just (Abs posinfo-gen b posinfo-gen x' atk T , star)
elab-typeh Γ (Iota pi pi' x T T') b =
  elab-typeh Γ T b ≫=maybe uncurry λ T k →
  rename x from Γ for λ x' →
  elab-typeh (ctxt-term-decl' pi' x' T Γ) (rename-var Γ x x' T') b ≫=maybe uncurry λ T' k' →
  just (Iota posinfo-gen posinfo-gen x' T T' , star)
elab-typeh Γ (Lft pi pi' x t lT) b = nothing
elab-typeh Γ (NoSpans T pi) b = nothing
elab-typeh Γ (TpApp T T') b =
  elab-typeh Γ T b ≫=maybe uncurry λ T k →
  elab-typeh Γ T' b ≫=maybe uncurry λ T' k' →
  case k of λ where
    (KndPi _ pi x (Tkk _) k'') → just (TpApp T T' , subst Γ T' x k'')
    _ → nothing
elab-typeh Γ (TpAppt T t) b =
  elab-typeh Γ T b ≫=maybe uncurry λ where
    T (KndPi _ pi x (Tkt T') k) →
      (if b then elab-check-term Γ t T' else elab-pure-term Γ (erase-term t)) ≫=maybe λ t →
      just (TpAppt T t , subst Γ t x k)
    _ _ → nothing
elab-typeh Γ (TpArrow T a T') b =
  elab-typeh Γ T b ≫=maybe uncurry λ T k →
  elab-typeh Γ T' b ≫=maybe uncurry λ T' k' →
  just (Abs posinfo-gen a posinfo-gen "_" (Tkt T) T' , star)
elab-typeh Γ (TpEq pi t t' pi') b =
  elab-pure-term Γ (erase-term t) ≫=maybe λ t →
  elab-pure-term Γ (erase-term t') ≫=maybe λ t' →
  just (mtpeq t t' , star)
elab-typeh Γ (TpHole pi) b = nothing
elab-typeh Γ (TpLambda pi pi' x atk T) b =
  elab-tkh Γ atk b ≫=maybe λ atk →
  rename x from Γ for λ x' →
  elab-typeh (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' T) b ≫=maybe uncurry λ T k →
  just (mtplam x' atk T , KndPi posinfo-gen posinfo-gen x' atk k)
elab-typeh Γ (TpParens pi T pi') b = elab-typeh Γ T b
elab-typeh Γ (TpVar pi x) b =
  ctxt-lookup-type-var' Γ x ≫=maybe λ k →
  elab-kindh Γ k b ≫=maybe λ k →
  just (mtpvar x , k)
elab-typeh Γ (TpLet pi (DefTerm pi' x ot t) T) = elab-typeh Γ (subst Γ (Chi posinfo-gen ot t) x T)
elab-typeh Γ (TpLet pi (DefType pi' x k T') T) = elab-typeh Γ (subst Γ T' x T)

elab-kindh Γ (KndArrow k k') b =
  elab-kindh Γ k b ≫=maybe λ k →
  elab-kindh Γ k' b ≫=maybe λ k' →
  just (KndPi posinfo-gen posinfo-gen "_" (Tkk k) k')
elab-kindh Γ (KndParens pi k pi') b = elab-kindh Γ k b
elab-kindh Γ (KndPi pi pi' x atk k) b =
  elab-tkh Γ atk b ≫=maybe λ atk →
  rename x from Γ for λ x' →
  elab-kindh (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' k) b ≫=maybe λ k →
  just (KndPi posinfo-gen posinfo-gen x' atk k)
elab-kindh Γ (KndTpArrow T k) b =
  elab-typeh Γ T b ≫=maybe uncurry λ T _ →
  elab-kindh Γ k b ≫=maybe λ k →
  just (KndPi posinfo-gen posinfo-gen "_" (Tkt T) k)
elab-kindh Γ (KndVar pi x as) b =
  ctxt-lookup-kind-var-def Γ x ≫=maybe uncurry (do-subst as)
  where
  do-subst : args → params → kind → maybe kind
  do-subst (ArgsCons (TermArg _ t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = do-subst ys ps (subst-kind Γ t x k)
  do-subst (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = do-subst ys ps (subst-kind Γ t x k)
  do-subst ArgsNil ParamsNil k = elab-kindh Γ k b
  do-subst _ _ _ = nothing
elab-kindh Γ (Star pi) b = just star

elab-tkh Γ (Tkt T) b = elab-typeh Γ T b ≫=maybe uncurry λ T _ → just (Tkt T)
elab-tkh Γ (Tkk k) b = elab-kindh Γ k b ≫=maybe λ k → just (Tkk k)

elab-pure-term Γ (Var pi x) = just (mvar x)
elab-pure-term Γ (App t NotErased t') = 
  elab-pure-term Γ t ≫=maybe λ t →
  elab-pure-term Γ t' ≫=maybe λ t' →
  just (App t NotErased t')
elab-pure-term Γ (Lam pi NotErased pi' x NoClass t) =
  rename x from Γ for λ x' →
  elab-pure-term (ctxt-var-decl pi x' Γ) (rename-var Γ x x' t) ≫=maybe λ t →
  just (mlam x' t)
elab-pure-term Γ (Let pi (DefTerm pi' x NoType t) t') =
  elab-pure-term Γ t ≫=maybe λ t →
  elab-pure-term Γ (subst Γ t x t')
elab-pure-term _ _ = nothing -- should be erased

elab-app-sols : ctxt → term → meta-vars → ℕ → maybe term
elab-app-sols Γ t Xs zero = just t
elab-app-sols Γ t Xs (suc n) =
  head2 (meta-vars.order Xs) ≫=maybe λ x →
  trie-lookup (meta-vars.varset Xs) x ≫=maybe λ X →
  case (meta-var.sol X) of λ where
    (meta-var-tm _ _) → nothing
    (meta-var-tp k mtp) →
      let id' = fresh-id-term Γ
          T = maybe-else (mtpeq id' id') id mtp in
      elab-type Γ T ≫=maybe uncurry λ T k →
      elab-app-sols Γ (AppTp t T) (drop-meta-var Xs) n

elab-app-term Γ (App t m t') =
  elab-app-term Γ t ≫=maybe uncurry' λ t T Xs →
  let abs-num = length (meta-vars.order Xs) in
  case meta-vars-unfold-tmapp Γ missing-span-location Xs T of λ where
    (Ys , (not-tmabs _)) → nothing
    (Ys , (yes-tmabs _ m' x Tₐ occ cod)) →
    -- (yes-tp-arrow* Ys T' Tₐ m' cod) →
      let Xs = meta-vars-add* Xs Ys
          cod = λ tm → if occ then subst-type Γ tm x cod else cod
          abs-num' = length (meta-vars.order Xs)
          num-apps = abs-num' ∸ abs-num
          ret t' cod' Xs = just (
            (λ Xs → t Xs ≫=maybe λ t →
              elab-app-sols Γ t (drop-meta-vars Xs abs-num) num-apps ≫=maybe λ t →
              just (App t m t')) ,
            cod' ,
            Xs) in
      case meta-vars-are-free-in-type Xs Tₐ of λ where
        ff → elab-hnf-type Γ Tₐ tt ≫=maybe λ Tₐ →
             elab-check-term Γ t' Tₐ ≫=maybe λ t' →
             ret t' (cod t') Xs
        tt → elab-hnf-type Γ Tₐ tt ≫=maybe λ Tₐ →
             elab-synth-term Γ t' ≫=maybe uncurry λ t' Tₐ' →
             case fst (match-types Xs empty-trie match-unfolding-both Tₐ Tₐ' Γ id-spans.empty-spans) of λ where
               (match-error _) → nothing
               (match-ok Xs) → ret t' (cod t') (meta-vars-update-kinds Γ Xs (meta-vars-in-type Xs Tₐ))

elab-app-term Γ (AppTp t T) =
  elab-type Γ T ≫=maybe uncurry λ T _ →
  elab-app-term Γ t ≫=maybe uncurry' λ t Tₕ Xs →
  case meta-vars-unfold-tpapp Γ Xs Tₕ of λ where
    (not-tpabs _) → nothing
    (yes-tpabs _ b x k Tₕ') →
    -- (yes-tp-abs _ b _ x k Tₕ') →
      let X = meta-var-fresh-tp Xs x missing-span-location (k , (just T))
          Tₕ'' = rename-var Γ x (meta-var-name X) Tₕ' in
      just ((λ Xs → t Xs ≫=maybe λ t → just (AppTp t T)) , Tₕ'' , meta-vars-add Xs X)

elab-app-term Γ (Parens pi t pi') = elab-app-term Γ t
elab-app-term Γ t =
  elab-synth-term Γ t ≫=maybe uncurry λ t T →
  just ((λ _ → just t) , T , meta-vars-empty)




{- ################################ IO ###################################### -}

elab-t : Set → Set
elab-t X = toplevel-state → (var-mapping file-mapping : renamectxt) → X → maybe (X × toplevel-state × renamectxt × renamectxt)

{-# TERMINATING #-}
elab-file' : elab-t string
elab-cmds : elab-t cmds
elab-params : elab-t params
elab-args : elab-t (args × params)
elab-imports : elab-t imports
elab-import : elab-t imprt

elab-params ts ρ φ ParamsNil = just (ParamsNil , ts , ρ , φ)
elab-params ts ρ φ (ParamsCons (Decl _ pi me x atk _) ps) =
  let Γ = toplevel-state.Γ ts in
  elab-tk Γ (subst-qualif Γ ρ atk) ≫=maybe λ atk →
  rename qualif-new-var Γ x - x from ρ for λ x' ρ →
  elab-params (record ts {Γ = ctxt-param-decl x x' atk Γ}) ρ φ ps ≫=maybe uncurry λ ps ts-ρ-φ →
  just (ParamsCons (Decl posinfo-gen posinfo-gen me x' atk posinfo-gen) ps , ts-ρ-φ)

elab-args ts ρ φ (ArgsNil , ParamsNil) = just ((ArgsNil , ParamsNil) , ts , ρ , φ)
elab-args ts ρ φ (_ , ParamsNil) = nothing -- Too many arguments
elab-args ts ρ φ (ArgsNil , ParamsCons p ps) = just ((ArgsNil , ParamsCons p ps) , ts , ρ , φ)
elab-args ts ρ φ (ArgsCons a as , ParamsCons (Decl _ _ me x atk _) ps) =
  let Γ = toplevel-state.Γ ts in
  case (a , atk) of λ where
    (TermArg me' t , Tkt T) →
      elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
      elab-check-term Γ (subst-qualif Γ ρ t) T ≫=maybe λ t →
      rename qualif-new-var Γ x - x lookup ρ for λ x' ρ →
      let ts = record ts {Γ = ctxt-term-def' x x' t T OpacTrans Γ} in
      elab-args ts ρ φ (as , ps) ≫=maybe (uncurry ∘ uncurry) λ as ps ts-ρ-φ →
      just ((ArgsCons (TermArg me' t) as , ParamsCons (Decl posinfo-gen posinfo-gen me x' (Tkt T) posinfo-gen) ps) , ts-ρ-φ)
    (TypeArg T , Tkk _) →
      elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
      rename qualif-new-var Γ x - x lookup ρ for λ x' ρ →
      let ts = record ts {Γ = ctxt-type-def' x x' T k OpacTrans Γ} in
      elab-args ts ρ φ (as , ps) ≫=maybe (uncurry ∘ uncurry) λ as ps ts-ρ-φ →
      just ((ArgsCons (TypeArg T) as , ParamsCons (Decl posinfo-gen posinfo-gen me x' (Tkk k) posinfo-gen) ps) , ts-ρ-φ)
    _ → nothing

elab-import ts ρ φ (Import _ op _ ifn oa as _) =
  let Γ = toplevel-state.Γ ts
      fn = ctxt-get-current-filename Γ
      mod = ctxt-get-current-mod Γ in
  get-include-elt-if ts fn ≫=maybe λ ie →
  trie-lookup (include-elt.import-to-dep ie) ifn ≫=maybe λ ifn' →
  elab-file' ts ρ φ ifn' ≫=maybe uncurry'' λ fn ts ρ φ →
  lookup-mod-params (toplevel-state.Γ ts) ifn' ≫=maybe λ ps →
  elab-args ts ρ φ (as , ps) ≫=maybe (uncurry' ∘ uncurry) λ as ps ts ρ-φ →
  let ts = fst (scope-file (record ts {Γ = ctxt-set-current-mod (toplevel-state.Γ ts) mod}) fn ifn' oa as) in
  just (Import posinfo-gen IsPublic posinfo-gen fn NoOptAs ArgsNil posinfo-gen , ts , ρ-φ)

elab-imports ts ρ φ ImportsStart = just (ImportsStart , ts , ρ , φ)
elab-imports ts ρ φ (ImportsNext i is) =
  elab-import ts ρ φ i ≫=maybe uncurry'' λ i ts ρ φ →
  elab-imports ts ρ φ is ≫=maybe uncurry λ is ts-ρ-φ →
  just (ImportsNext i is , ts-ρ-φ)

elab-cmds ts ρ φ CmdsStart = just (CmdsStart , ts , ρ , φ)
elab-cmds ts ρ φ (CmdsNext (DefTermOrType op (DefTerm _ x NoType t) _) cs) =
  let Γ = toplevel-state.Γ ts in
  elab-synth-term Γ (subst-qualif Γ ρ t) ≫=maybe uncurry λ t T →
  rename qualif-new-var Γ x - x from ρ for λ x' ρ →
  let ts = record ts {Γ = ctxt-term-def' x x' t T op Γ} in
  elab-cmds ts ρ φ cs ≫=maybe uncurry λ cs ts-ρ-φ →
  just (CmdsNext (DefTermOrType op (DefTerm posinfo-gen x' NoType t) posinfo-gen) cs , ts-ρ-φ)
elab-cmds ts ρ φ (CmdsNext (DefTermOrType op (DefTerm _ x (SomeType T) t) _) cs) =
  let Γ = toplevel-state.Γ ts in
  elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
  elab-check-term Γ (subst-qualif Γ ρ t) T ≫=maybe λ t →
  rename qualif-new-var Γ x - x from ρ for λ x' ρ →
  let ts = record ts {Γ = ctxt-term-def' x x' t T op Γ} in
  elab-cmds ts ρ φ cs ≫=maybe uncurry λ cs ts-ρ-φ →
  just (CmdsNext (DefTermOrType op (DefTerm posinfo-gen x' NoType t) posinfo-gen) cs , ts-ρ-φ)
elab-cmds ts ρ φ (CmdsNext (DefTermOrType op (DefType _ x _ T) _) cs) =
  let Γ = toplevel-state.Γ ts in
  elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
  rename qualif-new-var Γ x - x from ρ for λ x' ρ →
  let ts = record ts {Γ = ctxt-type-def' x x' T k op Γ} in
  elab-cmds ts ρ φ cs ≫=maybe uncurry λ cs ts-ρ-φ →
  just (CmdsNext (DefTermOrType op (DefType posinfo-gen x' k T) posinfo-gen) cs , ts-ρ-φ)
elab-cmds ts ρ φ (CmdsNext (DefKind _ x ps k _) cs) =
  let Γ = toplevel-state.Γ ts
      x' = fresh-var (qualif-new-var Γ x) (renamectxt-in-range ρ) ρ
      ρ = renamectxt-insert ρ x x' in
  let ts = record ts {Γ = ctxt-kind-def' x x' ps k Γ} in
  elab-cmds ts ρ φ cs
elab-cmds ts ρ φ (CmdsNext (ImportCmd i) cs) =
  elab-import ts ρ φ i ≫=maybe uncurry'' λ i ts ρ φ →
  elab-cmds ts ρ φ cs ≫=maybe uncurry λ cs ts-ρ-φ →
  just (CmdsNext (ImportCmd i) cs , ts-ρ-φ)

elab-file' ts ρ φ fn =
  get-include-elt-if ts fn ≫=maybe λ ie →
  case include-elt.need-to-add-symbols-to-context ie of λ where
    ff → rename fn - base-filename (takeFileName fn) lookup φ for λ fn' φ → just (fn' , ts , ρ , φ)
    tt → include-elt.ast ie ≫=maybe λ where
      (File _ is _ _ mn ps cs _) →
        rename fn - base-filename (takeFileName fn) from φ for λ fn' φ →
        let ie = record ie {need-to-add-symbols-to-context = ff; do-type-check = ff; inv = refl} in
        elab-imports (record (set-include-elt ts fn ie)
          {Γ = ctxt-set-current-file (toplevel-state.Γ ts) fn mn}) ρ φ is ≫=maybe uncurry'' λ is ts ρ φ →
        elab-params ts ρ φ ps ≫=maybe uncurry'' λ ps' ts ρ φ →
        let Γ = toplevel-state.Γ ts
            Γ = ctxt-add-current-params (ctxt-set-current-mod Γ (fn , mn , ps' , ctxt-get-qualif Γ)) in
        elab-cmds (record ts {Γ = Γ}) ρ φ cs ≫=maybe uncurry' λ cs ts ρ-φ →
        let ast = File posinfo-gen ImportsStart posinfo-gen posinfo-gen mn ParamsNil cs posinfo-gen in
        just (fn' , set-include-elt ts fn (ie-set-span-ast ie (toplevel-state.Γ ts) ast) , ρ-φ)

{-# TERMINATING #-}
elab-all : toplevel-state → (from-fp to-fp : string) → IO ⊤
elab-all ts fm to = elab-file' prep-ts empty-renamectxt empty-renamectxt fm err-code 1 else h
  where
  _err-code_else_ : ∀ {X : Set} → maybe X → ℕ → (X → IO ⊤) → IO ⊤
  nothing err-code n else f = putStrLn (ℕ-to-string n)
  just x err-code n else f = f x

  prep-ts : toplevel-state
  prep-ts = record ts
    {Γ = new-ctxt fm "[unknown]";
     is = trie-map (λ ie → record ie
         {need-to-add-symbols-to-context = tt;
          do-type-check = ff;
          inv = refl})
       (toplevel-state.is ts)}
  
  get-file-imports : toplevel-state → (filename : string) → stringset → maybe stringset
  get-file-imports ts fn is =
    get-include-elt-if ts fn ≫=maybe λ ie →
    foldr
      (λ fn' is → if fn =string fn' then is else
        (is ≫=maybe λ is →
        get-file-imports ts fn' is ≫=maybe λ is →
        just (stringset-insert is fn')))
      (just is)
      (include-elt.deps ie)

  h : (string × toplevel-state × renamectxt × renamectxt) → IO ⊤
  h' : toplevel-state → renamectxt → stringset → IO ⊤
  h (_ , ts , _ , φ) = get-file-imports ts fm (trie-single fm triv) err-code 3 else h' ts φ
  h' ts φ is = foldr
    (λ fn x → x >>= λ e →
      maybe-else
        (return ff)
        (λ fn-ie →
          writeRopeToFile (combineFileNames to (fst fn-ie) ^ ".ced")
            (maybe-else [[ "Error lookup up elaborated data" ]] id (ie-get-span-ast (snd fn-ie))) >>
          return e)
      (renamectxt-lookup φ fn ≫=maybe λ fn' →
      get-include-elt-if ts fn ≫=maybe λ ie →
      include-elt.ast ie ≫=maybe λ ast → just (fn' , ie)))
    (createDirectoryIfMissing tt to >> return tt)
    (stringset-strings is) >>= λ e →
    putStrLn (if e then "0" else "2")

elab-file : toplevel-state → (filename : string) → maybe rope
elab-file ts fn =
  elab-file' ts empty-renamectxt empty-renamectxt fn ≫=maybe uncurry'' λ fn' ts ρ φ →
  get-include-elt-if ts fn ≫=maybe ie-get-span-ast






{- Datatypes -}

parameters = 𝕃 decl

data indx : Set where
  Index : var → tk → indx
indices = 𝕃 indx

data ctr : Set where
  Ctr : var → type → ctr
constructors = 𝕃 ctr

data datatype : Set where
  Data : var → parameters → indices → constructors → datatype

{-# TERMINATING #-}
decompose-arrows : ctxt → type → parameters × type
decompose-arrows Γ (Abs pi me pi' x atk T) =
  rename-new x from Γ for λ x' →
  case decompose-arrows (ctxt-var-decl' x' Γ) (rename-var Γ x x' T) of λ where
    (ps , T') → Decl posinfo-gen posinfo-gen me x' atk posinfo-gen :: ps , T'
decompose-arrows Γ (TpArrow T me T') =
  rename-new "_" from Γ for λ x →
  case decompose-arrows (ctxt-var-decl' x Γ) T' of λ where
    (ps , T'') → Decl posinfo-gen posinfo-gen me x (Tkt T) posinfo-gen :: ps , T''
decompose-arrows Γ (TpParens pi T pi') = decompose-arrows Γ T
decompose-arrows Γ T = [] , T

decompose-ctr-type : ctxt → type → type × parameters × 𝕃 tty
decompose-ctr-type Γ T with decompose-arrows Γ T
...| ps , Tᵣ with decompose-tpapps Tᵣ
...| Tₕ , as = Tₕ , ps , as

{-# TERMINATING #-}
kind-to-indices : ctxt → kind → ctxt × indices
kind-to-indices Γ (KndArrow k k') =
  rename "x" from Γ for λ x' →
  let p = kind-to-indices (ctxt-var-decl' x' Γ) k' in
  fst p , Index x' (Tkk k) :: snd p
kind-to-indices Γ (KndParens pi k pi') = kind-to-indices Γ k
kind-to-indices Γ (KndPi pi pi' x atk k) =
  rename x from Γ for λ x' →
  let p = kind-to-indices (ctxt-var-decl' x' Γ) k in
  fst p , Index x atk :: snd p
kind-to-indices Γ (KndTpArrow T k) =
  rename "x" from Γ for λ x' →
  let p = kind-to-indices (ctxt-var-decl' x' Γ) k in
  fst p , Index x' (Tkt T) :: snd p
kind-to-indices Γ (KndVar pi x as) with ctxt-lookup-kind-var-def Γ x
...| nothing = Γ , []
...| just (ps , k) = kind-to-indices Γ $ subst-args-params Γ as ps k
kind-to-indices Γ (Star pi) = Γ , []

indices-to-kind : indices → kind → kind
indices-to-kind = flip $ foldr (λ {(Index x atk) → KndPi posinfo-gen posinfo-gen x atk})

parameters-to-kind : parameters → kind → kind
parameters-to-kind = flip $ foldr (λ {(Decl pi pi' me x atk pi'') → KndPi pi pi' x atk})

indices-to-tplams : indices → (body : type) → type
indices-to-tplams = flip $ foldr λ where
  (Index x atk) → TpLambda posinfo-gen posinfo-gen x atk

parameters-to-tplams : parameters → (body : type) → type
parameters-to-tplams = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → TpLambda pi pi' x atk

indices-to-alls : indices → (body : type) → type
indices-to-alls = flip $ foldr λ where
  (Index x atk) → Abs posinfo-gen Erased posinfo-gen x atk

parameters-to-alls : parameters → (body : type) → type
parameters-to-alls = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Abs pi me pi' x atk

indices-to-lams : indices → (body : term) → term
indices-to-lams = flip $ foldr λ where
  (Index x atk) → Lam posinfo-gen Erased posinfo-gen x (SomeClass atk)

parameters-to-lams : parameters → (body : term) → term
parameters-to-lams = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Lam pi me pi' x (SomeClass atk)

parameters-to-lams' : parameters → (body : term) → term
parameters-to-lams' = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Lam pi me pi' x NoClass

constructors-to-lams' : constructors → (body : term) → term
constructors-to-lams' = flip $ foldr λ where
  (Ctr x T) → Lam posinfo-gen NotErased posinfo-gen x NoClass

indices-to-apps : indices → (body : term) → term
indices-to-apps = flip $ foldl λ where
  (Index x (Tkt T)) t → App t Erased (mvar x)
  (Index x (Tkk k)) t → AppTp t (mtpvar x)

parameters-to-apps : parameters → (body : term) → term
parameters-to-apps = flip $ foldl λ where --↓ ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ←
  (Decl pi pi' me x (Tkt T) pi'') t → App t me (mvar x)  --                             ↑
  (Decl pi pi' me x (Tkk k) pi'') t → AppTp t (mtpvar x) --                             ↑
-- TODO: Should the user really be given the option to have parameters erased or not? → ↑

indices-to-tpapps : indices → (body : type) → type
indices-to-tpapps = flip $ foldl λ where
  (Index x (Tkt T)) T' → TpAppt T' (mvar x)
  (Index x (Tkk k)) T  → TpApp  T  (mtpvar x)

parameters-to-tpapps : parameters → (body : type) → type
parameters-to-tpapps = flip $ foldl λ where
  (Decl pi pi' me x (Tkt T) pi'') T' → TpAppt T' (mvar x)
  (Decl pi pi' me x (Tkk k) pi'') T  → TpApp  T  (mtpvar x)

constructors-to-lams : ctxt → var → parameters → constructors → (body : term) → term
constructors-to-lams Γ x ps cs t = foldr (λ {(Ctr y T) f Γ → Lam posinfo-gen NotErased posinfo-gen y (SomeClass $ Tkt $ subst-type Γ (parameters-to-tpapps ps $ mtpvar y) y T) $ f $ ctxt-var-decl' y Γ}) (λ Γ → t) cs Γ

add-ps-to-ctxt : ctxt → parameters → ctxt
add-ps-to-ctxt = foldr (λ {(Decl _ _ _ x'' _ _) → ctxt-var-decl' x''})

recompose-apps : 𝕃 tty → term → term
recompose-apps [] h = h
recompose-apps ((tterm t') :: args) h = App (recompose-apps args h) Erased t'
recompose-apps ((ttype t') :: args) h = AppTp (recompose-apps args h) t'


mk-erased-ctr : ctxt → ℕ → constructors → 𝕃 term → maybe term
mk-erased-ctr Γ n cs as = mk-erased-ctrh Γ (inj₁ n) cs as [] where
  mk-erased-ctrh : ctxt → ℕ ⊎ var → constructors → 𝕃 term → 𝕃 var → maybe term
  mk-erased-ctrh Γ (inj₁ zero) (Ctr x _ :: cs) as xs = rename x from Γ for λ x' →
    mk-erased-ctrh (ctxt-var-decl' x' Γ) (inj₂ x') cs as (x' :: xs)
  mk-erased-ctrh Γ (inj₁ (suc n)) (Ctr x _ :: cs) as xs = rename x from Γ for λ x' →
    mk-erased-ctrh (ctxt-var-decl' x' Γ) (inj₁ n) cs as (x' :: xs)
  mk-erased-ctrh Γ (inj₂ xₕ) (Ctr x _ :: cs) as xs = rename x from Γ for λ x' →
    mk-erased-ctrh (ctxt-var-decl' x' Γ) (inj₂ xₕ) cs as (x' :: xs)
  mk-erased-ctrh Γ (inj₁ _) [] as xs = nothing
  mk-erased-ctrh Γ (inj₂ xₕ) [] as xs =
    just $ foldl mlam (foldr (flip mapp) (mvar xₕ) as) $ xs

get-ctr-in-ctrs : var → constructors → maybe ℕ
get-ctr-in-ctrs x cs = h zero cs where
  h : ℕ → constructors → maybe ℕ
  h n [] = nothing
  h n (Ctr y _ :: cs) = if x =string y then just n else h (suc n) cs

mk-ctr-untyped-beta : ctxt → var → constructors → parameters → term
mk-ctr-untyped-beta Γ x cs ps =
  maybe-else
    (mvar "error-making-untyped-beta")
    (λ t → Beta posinfo-gen NoTerm $ SomeTerm t posinfo-gen) $
    get-ctr-in-ctrs x cs ≫=maybe λ n → mk-erased-ctr Γ n cs $
      foldl (λ {(Decl pi pi' NotErased x (Tkt T) pi'') ts → mvar x :: ts; p ts → ts}) [] ps

mk-ctr-type : ctxt → ctr → (head : var) → constructors → type
mk-ctr-type Γ (Ctr x T) Tₕ cs with decompose-ctr-type Γ T
...| Tₓ , ps , is =
  foldr
    (λ {(Decl pi pi' NotErased y atk pi'') f as →
          Abs pi NotErased pi' y atk $ f (mvar y :: as);
        (Decl pi pi' Erased y atk pi'') f as →
          Abs pi Erased pi' y atk $ f as})
    (λ as → curry recompose-tpapps
      (TpAppt (mtpvar Tₕ) $ maybe-else
        (mvar "error-making-ctr-type-beta")
        (λ t → Beta posinfo-gen NoTerm $ SomeTerm t posinfo-gen)
        (get-ctr-in-ctrs x cs ≫=maybe λ n → mk-erased-ctr Γ n cs as)) is) ps []

Top-type = mtpeq (mlam "x" $ mvar "x") (mlam "x" $ mvar "x")

record mendler-names : Set where
  field
    F : var
    fmap : var
    Cast : var
    cast : var
    Functor : var
    AlgM : var
    FixM : var
    inFixM : var
    PrfAlgM : var
    IsIndFixM : var
    FixIndM : var
    inFixIndM : var
    LiftM : var
    LiftProp1 : var
    LiftProp2 : var
    LiftProp3 : var
    LiftProp4 : var
    convIH : var
    MendlerInd : var
    Ind : var

choose-mendler-names : var → ctxt → ctxt × mendler-names
choose-mendler-names x =
  choose "F" λ F →
  choose "Fmap" λ fmap →
  choose "Cast" λ Cast →
  choose "cast" λ cast →
  choose "Functor" λ Functor →
  choose "AlgM" λ AlgM →
  choose "FixM" λ FixM →
  choose "inFixM" λ inFixM →
  choose "PrfAlgM" λ PrfAlgM →
  choose "IsIndFixM" λ IsIndFixM →
  choose "FixIndM" λ FixIndM →
  choose "inFixIndM" λ inFixIndM →
  choose "LiftM" λ LiftM →
  choose "LiftProp1" λ LiftProp1 →
  choose "LiftProp2" λ LiftProp2 →
  choose "LiftProp3" λ LiftProp3 →
  choose "LiftProp4" λ LiftProp4 →
  choose "convIH" λ convIH →
  choose "MendlerInd" λ MendlerInd →
  choose "Ind" λ Ind Γ →
  Γ , record {F = F; fmap = fmap; Cast = Cast; cast = cast; Functor = Functor; AlgM = AlgM;
              FixM = FixM; inFixM = inFixM; PrfAlgM = PrfAlgM; IsIndFixM = IsIndFixM;
              FixIndM = FixIndM; inFixIndM = inFixIndM; LiftM = LiftM;
              LiftProp1 = LiftProp1; LiftProp2 = LiftProp2; LiftProp3 = LiftProp3;
              LiftProp4 = LiftProp4; convIH = convIH; MendlerInd = MendlerInd; Ind = Ind}
  where
  choose : ∀ {X : Set} → var → (var → ctxt → X) → ctxt → X
  choose y f Γ = rename (x ^ y) from Γ for λ z → f z $ ctxt-var-decl' z Γ

add-datatype-vars-to-ctxt : ctxt → datatype → ctxt
add-datatype-vars-to-ctxt Γ (Data x ps is cs) =
  foldr (λ {(Ctr x _) → ctxt-var-decl' x})
    (foldr (λ {(Index x _) → ctxt-var-decl' x})
      (foldr (λ {(Decl _ _ _ x _ _) → ctxt-var-decl' x}) Γ ps) is) cs

mk-mendler-defs : ctxt → datatype → cmds
mk-mendler-defs Γₒ (Data x ps is cs) =
  csn Cast $
  csn cast $
  csn Functor $
  csn AlgM $
  csn FixM $
  csn inFixM $
  csn PrfAlgM $
  csn IsIndFixM $
  csn FixIndM $
  csn inFixIndM $
  csn LiftM $
  csn LiftProp1 $
  csn LiftProp2 $
  csn LiftProp3 $
  csn LiftProp4 $
  csn convIH $
  csn MendlerInd $
  csn type-functor $
  csn type-fmap $
  csn type-actual $
  type-ctrs-ind
  where
  Γ' = add-datatype-vars-to-ctxt Γₒ (Data x ps is cs)
  Γ-ns = choose-mendler-names x Γ'
  Γ = fst Γ-ns
  ns = snd Γ-ns

  csn = CmdsNext ∘ flip (DefTermOrType OpacTrans) posinfo-gen
  Aₓ = rename "A" from Γ for id
  Bₓ = rename "B" from Γ for id
  Fₓ = rename "F" from Γ for id
  Rₓ = rename "R" from Γ for id
  Xₓ = rename "X" from Γ for id
  Qₓ = rename "Q" from Γ for id
  Yₓ = rename "Y" from Γ for id
  Y1ₓ = rename "Yprop1" from Γ for id
  Y2ₓ = rename "Yprop2" from Γ for id
  Y3ₓ = rename "Yprop3" from Γ for id
  Y4ₓ = rename "Yprop4" from Γ for id
  algₓ = rename "alg" from Γ for id
  fixₓ = rename "fix" from Γ for id
  fmapₓ = rename "fmap" from Γ for id
  cₓ = rename "c" from Γ for id
  eₓ = rename "e" from Γ for id
  rₓ = rename "r" from Γ for id
  yₓ = rename "y" from Γ for id
  zₓ = rename "z" from Γ for id
  qₓ = rename "q" from Γ for id
  fₓ = rename "f" from Γ for id
  gₓ = rename "g" from Γ for id
  hₓ = rename "h" from Γ for id
  iₓ = rename "i" from Γ for id
  c2ₓ = rename "c2" from Γ for id
  ihₓ = rename "ih" from Γ for id

  k = indices-to-kind is $ Star posinfo-gen

  Cast =
    DefType posinfo-gen (mendler-names.Cast ns)
      (KndArrow k $ KndArrow k star) $
      TpLambda posinfo-gen posinfo-gen Aₓ (Tkk k) $
      TpLambda posinfo-gen posinfo-gen Bₓ (Tkk k) $
      Iota posinfo-gen posinfo-gen fₓ
        (indices-to-alls is $
         TpArrow (indices-to-tpapps is (mtpvar Aₓ))
           NotErased (indices-to-tpapps is (mtpvar Bₓ))) $
        mtpeq (mvar fₓ) $ fresh-id-term Γ

  cast = DefTerm posinfo-gen (mendler-names.cast ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Aₓ (SomeClass (Tkk k)) $
    Lam posinfo-gen Erased posinfo-gen Bₓ (SomeClass (Tkk k)) $
    Lam posinfo-gen Erased posinfo-gen fₓ (SomeClass $ Tkt $
      TpApp (TpApp (mtpvar $ mendler-names.Cast ns) $ mtpvar Aₓ) $ mtpvar Bₓ) $
    Phi posinfo-gen (IotaProj (mvar fₓ) "2" posinfo-gen)
      (IotaProj (mvar fₓ) "1" posinfo-gen) (fresh-id-term Γ) posinfo-gen

  Functor = DefType posinfo-gen (mendler-names.Functor ns)
    (KndArrow (KndArrow k k) star)
    (TpLambda posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
     Abs posinfo-gen Erased posinfo-gen Aₓ (Tkk k) $
     Abs posinfo-gen Erased posinfo-gen Bₓ (Tkk k) $ 
     TpArrow (TpApp (TpApp (mtpvar $ mendler-names.Cast ns)
                (mtpvar Aₓ)) (mtpvar Bₓ)) Erased $
       (TpApp (TpApp (mtpvar $ mendler-names.Cast ns)
         (TpApp (mtpvar Fₓ) (mtpvar Aₓ)))
         (TpApp (mtpvar Fₓ) (mtpvar Bₓ))))

  AlgM = DefType posinfo-gen (mendler-names.AlgM ns)
    (KndArrow (KndArrow k k) (KndArrow star k)) $
    TpLambda posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
    TpLambda posinfo-gen posinfo-gen Aₓ (Tkk star) $
    indices-to-tplams is $
    Abs posinfo-gen Erased posinfo-gen Rₓ (Tkk $ k) $
    TpArrow (TpArrow (indices-to-tpapps is $ mtpvar Rₓ) NotErased $ mtpvar Aₓ) NotErased $
    TpArrow (indices-to-tpapps is $ TpApp (mtpvar Fₓ) $ mtpvar Rₓ) NotErased $ mtpvar Aₓ

  FixM = DefType posinfo-gen (mendler-names.FixM ns) (KndArrow (KndArrow k k) k) $
    TpLambda posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
    indices-to-tplams is $
    Abs posinfo-gen Erased posinfo-gen Aₓ (Tkk star) $
    TpArrow
      (indices-to-tpapps is $
        TpApp (TpApp (mtpvar $ mendler-names.AlgM ns) (mtpvar Fₓ)) (mtpvar Aₓ))
      NotErased $ mtpvar Aₓ
  
  inFixM = DefTerm posinfo-gen (mendler-names.inFixM ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    indices-to-lams is $
    Lam posinfo-gen NotErased posinfo-gen fₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpApp (mtpvar Fₓ) (TpApp (mtpvar $ mendler-names.FixM ns) (mtpvar Fₓ))) $
    Lam posinfo-gen Erased posinfo-gen Aₓ (SomeClass $ Tkk star) $
    Lam posinfo-gen NotErased posinfo-gen algₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpApp (TpApp (mtpvar $ mendler-names.AlgM ns) (mtpvar Fₓ)) (mtpvar Aₓ)) $
    App (App (AppTp (mvar algₓ) (TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ))
      NotErased $ Lam posinfo-gen NotErased posinfo-gen fixₓ (SomeClass $ Tkt $
        indices-to-tpapps is $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
        App (AppTp (mvar fixₓ) $ mtpvar Aₓ) NotErased $ mvar algₓ) NotErased $ mvar fₓ

  PrfAlgM =
    let k1 = Tkk $ KndArrow k k
        k2 = Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ
        k3 = Tkk k
        k4 = Tkk $ indices-to-kind is $ KndTpArrow
          (indices-to-tpapps is $ mtpvar Xₓ) $ star
        k5 = Tkt $ indices-to-alls is $ TpArrow
          (indices-to-tpapps is $ TpApp (mtpvar Fₓ) $ mtpvar Xₓ) NotErased $
          indices-to-tpapps is $ mtpvar Xₓ in
    DefType posinfo-gen (mendler-names.PrfAlgM ns)
      (KndPi posinfo-gen posinfo-gen Fₓ k1 $
       KndPi posinfo-gen posinfo-gen ignored-var k2 $
       KndPi posinfo-gen posinfo-gen Xₓ k3 $
       KndPi posinfo-gen posinfo-gen ignored-var k4 $
       KndPi posinfo-gen posinfo-gen ignored-var k5 $
       star) $
      TpLambda posinfo-gen posinfo-gen Fₓ k1 $
      TpLambda posinfo-gen posinfo-gen fmapₓ k2 $
      TpLambda posinfo-gen posinfo-gen Xₓ k3 $
      TpLambda posinfo-gen posinfo-gen Qₓ k4 $
      TpLambda posinfo-gen posinfo-gen algₓ k5 $
      Abs posinfo-gen Erased posinfo-gen Rₓ (Tkk k) $
      Abs posinfo-gen Erased posinfo-gen cₓ
        (Tkt $ TpApp (TpApp (mtpvar $ mendler-names.Cast ns) (mtpvar Rₓ)) (mtpvar Xₓ)) $
      TpArrow (indices-to-alls is $ Abs posinfo-gen NotErased posinfo-gen rₓ
        (Tkt $ indices-to-tpapps is $ mtpvar Rₓ) $
        TpAppt (indices-to-tpapps is $ mtpvar Qₓ) (App (indices-to-apps is $
          App (AppTp (AppTp (mvar $ mendler-names.cast ns) $ mtpvar Rₓ) $ mtpvar Xₓ)
            Erased $ mvar cₓ) NotErased $ mvar rₓ)) NotErased $
      indices-to-alls is $ Abs posinfo-gen NotErased posinfo-gen fₓ
        (Tkt $ indices-to-tpapps is $ TpApp (mtpvar Fₓ) $ mtpvar Rₓ) $
      TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $
      App (indices-to-apps is $ mvar algₓ) NotErased $
      App (indices-to-apps is $ App
          (AppTp (AppTp (mvar $ mendler-names.cast ns) $ TpApp (mtpvar Fₓ) $ mtpvar Rₓ) $
             TpApp (mtpvar Fₓ) $ mtpvar Xₓ) Erased $
          App (AppTp (AppTp (mvar fmapₓ) $ mtpvar Rₓ) $ mtpvar Xₓ) Erased $ mvar cₓ)
        NotErased $ mvar fₓ
  
  IsIndFixM = DefType posinfo-gen (mendler-names.IsIndFixM ns)
    (KndPi posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
     KndTpArrow (TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
     indices-to-kind is $ KndTpArrow (indices-to-tpapps is $
       TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) star) $
    TpLambda posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
    TpLambda posinfo-gen posinfo-gen fmapₓ
      (Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
    indices-to-tplams is $
    TpLambda posinfo-gen posinfo-gen yₓ
      (Tkt $ indices-to-tpapps is $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
    Abs posinfo-gen Erased posinfo-gen Qₓ (Tkk $ indices-to-kind is $ KndTpArrow
      (indices-to-tpapps is $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) star) $
    TpArrow (TpAppt (TpApp (TpApp (TpAppt (TpApp (mtpvar $ mendler-names.PrfAlgM ns) $
          mtpvar Fₓ) $ mvar fmapₓ) $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
        mtpvar Qₓ) $ AppTp (mvar $ mendler-names.inFixM ns) $ mtpvar Fₓ)
      NotErased $ TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $ mvar yₓ
  
  FixIndM = DefType posinfo-gen (mendler-names.FixIndM ns)
    (KndPi posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
     KndTpArrow (TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) k) $
    TpLambda posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
    TpLambda posinfo-gen posinfo-gen fmapₓ
      (Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
    indices-to-tplams is $
    Iota posinfo-gen posinfo-gen yₓ
      (indices-to-tpapps is $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
      (TpAppt (indices-to-tpapps is $ TpAppt (TpApp (mtpvar $ mendler-names.IsIndFixM ns) $
        mtpvar Fₓ) $ mvar fmapₓ) $ mvar yₓ)
  
  inFixIndM = DefTerm posinfo-gen (mendler-names.inFixIndM ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    Lam posinfo-gen Erased posinfo-gen fmapₓ
      (SomeClass $ Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
    indices-to-lams is $
    Lam posinfo-gen NotErased posinfo-gen fₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpApp (mtpvar Fₓ) $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $
      mvar fmapₓ) $
    Let posinfo-gen (DefTerm posinfo-gen cₓ
      (SomeType (TpApp (TpApp (mtpvar $ mendler-names.Cast ns) $
           TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
         TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ)) $
      IotaPair posinfo-gen
        (indices-to-lams is $ Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
           IotaProj (mvar yₓ) "1" posinfo-gen)
        (Beta posinfo-gen NoTerm NoTerm) NoGuide posinfo-gen) $
    Chi posinfo-gen (SomeType $ indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
    IotaPair posinfo-gen (App (indices-to-apps is $ AppTp (mvar $ mendler-names.inFixM ns) $
      mtpvar Fₓ) NotErased $
      
      App (indices-to-apps is $ App (AppTp (AppTp (mvar $ mendler-names.cast ns) $
        TpApp (mtpvar Fₓ) $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $
          mvar fmapₓ) $
        TpApp (mtpvar Fₓ) $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) Erased $
        App (AppTp (AppTp (mvar fmapₓ) $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $
        mtpvar Fₓ) $ mvar fmapₓ) $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) Erased
        $ mvar cₓ) NotErased $ mvar fₓ)
      (Lam posinfo-gen Erased posinfo-gen Qₓ NoClass $
       Lam posinfo-gen NotErased posinfo-gen qₓ NoClass $
       App (indices-to-apps is $ App (App (AppTp (mvar qₓ) $
         TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) Erased
         $ mvar cₓ) NotErased $ indices-to-lams is $
         Lam posinfo-gen NotErased posinfo-gen rₓ NoClass $ App (AppTp
           (IotaProj (mvar rₓ) "2" posinfo-gen) $ mtpvar Qₓ) NotErased $ mvar qₓ)
         NotErased $ mvar fₓ)
      NoGuide posinfo-gen

  LiftM =
    let k' = indices-to-kind is $ KndTpArrow (indices-to-tpapps is $
          TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) star
        T = indices-to-tpapps is $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ
        T' = indices-to-tpapps is $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $
          mtpvar Fₓ) $ mvar fmapₓ in
    DefType posinfo-gen (mendler-names.LiftM ns)
    (KndPi posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
     KndPi posinfo-gen posinfo-gen fmapₓ
       (Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
     KndArrow k' $ indices-to-kind is $ KndTpArrow T star) $
    TpLambda posinfo-gen posinfo-gen Fₓ (Tkk $ KndArrow k k) $
    TpLambda posinfo-gen posinfo-gen fmapₓ
      (Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
    TpLambda posinfo-gen posinfo-gen Qₓ (Tkk k') $
    indices-to-tplams is $
    TpLambda posinfo-gen posinfo-gen fₓ (Tkt T) $
    Iota posinfo-gen posinfo-gen gₓ (Top-type) $
    Abs posinfo-gen Erased posinfo-gen Xₓ (Tkk $ KndTpArrow (Top-type) star) $
    TpArrow (Abs posinfo-gen NotErased posinfo-gen yₓ (Tkt T') $
      Abs posinfo-gen NotErased posinfo-gen hₓ
        (Tkt $ Iota posinfo-gen posinfo-gen ignored-var (mtpeq (mvar fₓ) $ mvar yₓ)
          (TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $ mvar yₓ)) $
        TpAppt (mtpvar Xₓ) $ Beta posinfo-gen NoTerm $
          SomeTerm (mlam iₓ $ mapp (mapp (mvar iₓ) $ mvar yₓ) $ mvar hₓ) posinfo-gen)
      NotErased $ TpAppt (mtpvar Xₓ) $ mvar gₓ
  
  LiftProp1 = DefTerm posinfo-gen (mendler-names.LiftProp1 ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    Lam posinfo-gen Erased posinfo-gen fmapₓ
      (SomeClass $ Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) (mtpvar Fₓ)) $
    Lam posinfo-gen Erased posinfo-gen Qₓ (SomeClass $ Tkk $ indices-to-kind is $
      KndTpArrow (indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) star) $
    indices-to-lams is $
    Lam posinfo-gen Erased posinfo-gen fₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
    Lam posinfo-gen NotErased posinfo-gen rₓ
      (SomeClass $ Tkt $ TpAppt (indices-to-tpapps is $ TpApp (TpAppt (TpApp
        (mtpvar $ mendler-names.LiftM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $ mtpvar Qₓ) $
          IotaProj (mvar fₓ) "1" posinfo-gen) $
    App (AppTp (IotaProj (mvar rₓ) "2" posinfo-gen) $ TpLambda posinfo-gen posinfo-gen ignored-var (Tkt Top-type) $ TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $ mvar fₓ) NotErased $
    Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
    Lam posinfo-gen NotErased posinfo-gen qₓ NoClass $
    Rho posinfo-gen RhoPlain NoNums (IotaProj (mvar qₓ) "1" posinfo-gen) NoGuide $
    IotaProj (mvar qₓ) "2" posinfo-gen

  LiftProp2 = DefTerm posinfo-gen (mendler-names.LiftProp2 ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    Lam posinfo-gen Erased posinfo-gen fmapₓ
      (SomeClass $ Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) (mtpvar Fₓ)) $
    Lam posinfo-gen Erased posinfo-gen Qₓ (SomeClass $ Tkk $ indices-to-kind is $
      KndTpArrow (indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) star) $
    indices-to-lams is $
    Lam posinfo-gen NotErased posinfo-gen fₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
    Lam posinfo-gen NotErased posinfo-gen rₓ
      (SomeClass $ Tkt $ TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $ mvar fₓ) $
    Chi posinfo-gen (SomeType $ TpAppt (indices-to-tpapps is $
      TpApp (TpAppt (TpApp (mtpvar $ mendler-names.LiftM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
      mtpvar Qₓ) $ IotaProj (mvar fₓ) "1" posinfo-gen) $
    IotaPair posinfo-gen (Beta posinfo-gen NoTerm $ SomeTerm
      (mlam gₓ $ mapp (mapp (mvar gₓ) $ mvar fₓ) $ mvar rₓ) posinfo-gen)
    (Lam posinfo-gen Erased posinfo-gen Xₓ NoClass $
     Lam posinfo-gen NotErased posinfo-gen gₓ NoClass $
     App (App (mvar gₓ) NotErased $ mvar fₓ) NotErased $ IotaPair posinfo-gen
       (Beta posinfo-gen NoTerm $ SomeTerm (mvar rₓ) posinfo-gen)
       (mvar rₓ) NoGuide posinfo-gen) NoGuide posinfo-gen

  LiftProp3 = DefTerm posinfo-gen (mendler-names.LiftProp3 ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    Lam posinfo-gen Erased posinfo-gen fmapₓ
      (SomeClass $ Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) (mtpvar Fₓ)) $
    Lam posinfo-gen Erased posinfo-gen Qₓ (SomeClass $ Tkk $ indices-to-kind is $
      KndTpArrow (indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) star) $
    indices-to-lams is $
    Lam posinfo-gen Erased posinfo-gen fₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
    Lam posinfo-gen NotErased posinfo-gen rₓ
      (SomeClass $ Tkt $ TpAppt
        (indices-to-tpapps is $ TpApp (TpAppt (TpApp (mtpvar $ mendler-names.LiftM ns) $
          mtpvar Fₓ) $ mvar fmapₓ) $ mtpvar Qₓ) $ mvar fₓ) $
    App (AppTp (IotaProj (mvar rₓ) "2" posinfo-gen) $
      TpLambda posinfo-gen posinfo-gen ignored-var (Tkt Top-type) $
      indices-to-tpapps is $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $
        mvar fmapₓ) NotErased $
    Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
    Lam posinfo-gen NotErased posinfo-gen qₓ NoClass $
    mvar yₓ

  LiftProp4 = DefTerm posinfo-gen (mendler-names.LiftProp4 ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    Lam posinfo-gen Erased posinfo-gen fmapₓ
      (SomeClass $ Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) (mtpvar Fₓ)) $
    Lam posinfo-gen Erased posinfo-gen Qₓ (SomeClass $ Tkk $ indices-to-kind is $
      KndTpArrow (indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) star) $
    indices-to-lams is $
    Lam posinfo-gen Erased posinfo-gen fₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
    Lam posinfo-gen Erased posinfo-gen rₓ (SomeClass $ Tkt $
      TpAppt (indices-to-tpapps is $
        TpApp (TpAppt (TpApp (mtpvar $ mendler-names.LiftM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
          mtpvar Qₓ) $ mvar fₓ) $
    Chi posinfo-gen (SomeType $ mtpeq (mapp (mvar $ mendler-names.LiftProp3 ns) $ mvar rₓ) $ mvar fₓ) $
    Rho posinfo-gen RhoPlain NoNums
      (App (AppTp (IotaProj (mvar rₓ) "2" posinfo-gen) $
        TpLambda posinfo-gen posinfo-gen yₓ (Tkt Top-type) $
        mtpeq (mapp (mvar $ mendler-names.LiftProp3 ns) $ mvar yₓ) $ mvar fₓ) NotErased $
      Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
      Lam posinfo-gen NotErased posinfo-gen qₓ NoClass $
      Sigma posinfo-gen $
      IotaProj (mvar qₓ) "1" posinfo-gen) NoGuide $
    Beta posinfo-gen NoTerm NoTerm

  convIH = DefTerm posinfo-gen (mendler-names.convIH ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    Lam posinfo-gen Erased posinfo-gen fmapₓ
      (SomeClass $ Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
    Lam posinfo-gen Erased posinfo-gen Qₓ
      (SomeClass $ Tkk $ indices-to-kind is $ KndTpArrow (indices-to-tpapps is $
        TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) star) $
    Lam posinfo-gen Erased posinfo-gen Yₓ
      (SomeClass $ Tkk $ indices-to-kind is $ KndTpArrow
        (indices-to-tpapps is $ TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) star) $
    Lam posinfo-gen NotErased posinfo-gen Y1ₓ (SomeClass $ Tkt $ indices-to-alls is $
      Abs posinfo-gen Erased posinfo-gen fₓ (Tkt $ indices-to-tpapps is $
        TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
        TpArrow (TpAppt (indices-to-tpapps is $ mtpvar Yₓ) $
            IotaProj (mvar fₓ) "1" posinfo-gen) NotErased $
          TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $ mvar fₓ) $
    Lam posinfo-gen NotErased posinfo-gen Y2ₓ (SomeClass $ Tkt $ indices-to-alls is $
      Abs posinfo-gen NotErased posinfo-gen fₓ (Tkt $ indices-to-tpapps is $
        TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
        TpArrow (TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $ mvar fₓ) NotErased $ (TpAppt (indices-to-tpapps is $ mtpvar Yₓ) $
            IotaProj (mvar fₓ) "1" posinfo-gen)) $
    Lam posinfo-gen NotErased posinfo-gen Y3ₓ (SomeClass $ Tkt $ indices-to-alls is $
      Abs posinfo-gen Erased posinfo-gen fₓ (Tkt $ indices-to-tpapps is $
        TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
        TpArrow (TpAppt (indices-to-tpapps is $ mtpvar Yₓ) $ mvar fₓ) NotErased $
          indices-to-tpapps is $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
    Lam posinfo-gen NotErased posinfo-gen Y4ₓ (SomeClass $ Tkt $ indices-to-alls is $
      Abs posinfo-gen Erased posinfo-gen fₓ (Tkt $ indices-to-tpapps is $
        TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $
        Abs posinfo-gen Erased posinfo-gen rₓ
          (Tkt $ TpAppt (indices-to-tpapps is $ mtpvar Yₓ) $ mvar fₓ) $
          mtpeq (mapp (mvar Y3ₓ) $ mvar rₓ) $ mvar fₓ) $
    Lam posinfo-gen NotErased posinfo-gen qₓ
      (SomeClass $ Tkt $ TpAppt (TpApp (TpApp (TpAppt (TpApp
        (mtpvar $ mendler-names.PrfAlgM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
        TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
        mtpvar Qₓ) $ App (AppTp (mvar $ mendler-names.inFixIndM ns) $ mtpvar Fₓ) Erased $
        mvar fmapₓ) $
    Chi posinfo-gen (SomeType $ TpAppt (TpApp (TpApp (TpAppt (TpApp
        (mtpvar $ mendler-names.PrfAlgM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
        TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) $ mtpvar Yₓ) $
        AppTp (mvar $ mendler-names.inFixM ns) $ mtpvar Fₓ) $
    Lam posinfo-gen Erased posinfo-gen Rₓ NoClass $
    Lam posinfo-gen Erased posinfo-gen cₓ NoClass $
    Lam posinfo-gen NotErased posinfo-gen ihₓ NoClass $
    indices-to-lams is $
    Lam posinfo-gen NotErased posinfo-gen rₓ NoClass $
    Let posinfo-gen (DefTerm posinfo-gen c2ₓ
      (SomeType $ TpApp (TpApp (mtpvar $ mendler-names.Cast ns) $ mtpvar Rₓ) $
         TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
      IotaPair posinfo-gen
        (indices-to-lams is $ Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
           Phi posinfo-gen
             (App (App (indices-to-apps is $ mvar Y4ₓ) Erased $
               App (indices-to-apps is $ App (AppTp (AppTp
                     (mvar $ mendler-names.cast ns) $ mtpvar Rₓ) $
                   TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) Erased $ mvar cₓ)
                 NotErased $ mvar yₓ) Erased $
               App (indices-to-apps is $ mvar ihₓ) NotErased $ mvar yₓ)
             (App (App (indices-to-apps is $ mvar Y3ₓ) Erased $
               App (indices-to-apps is $ App (AppTp (AppTp
                     (mvar $ mendler-names.cast ns) $ mtpvar Rₓ) $
                   TpApp (mtpvar $ mendler-names.FixM ns) $ mtpvar Fₓ) Erased $ mvar cₓ)
                 NotErased $ mvar yₓ) NotErased $
               App (indices-to-apps is $ mvar ihₓ) NotErased $ mvar yₓ)
             (mvar yₓ) posinfo-gen) (Beta posinfo-gen NoTerm NoTerm) NoGuide posinfo-gen) $
    App (App (indices-to-apps is $ mvar Y2ₓ) NotErased $ App (indices-to-apps is $
      App (AppTp (mvar $ mendler-names.inFixIndM ns) $ mtpvar Fₓ) Erased $ mvar fmapₓ)
        NotErased $ App (indices-to-apps is $ App (AppTp (AppTp
          (mvar $ mendler-names.cast ns) $
          TpApp (mtpvar Fₓ) $ mtpvar Rₓ) $ TpApp (mtpvar Fₓ) $
            TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ)
          Erased $ App (AppTp (AppTp (mvar fmapₓ) $ mtpvar Rₓ) $
            TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ)
              Erased $ mvar c2ₓ) NotErased $ mvar rₓ) NotErased $
    App (indices-to-apps is $ App (App (mvar qₓ) Erased $ mvar c2ₓ) NotErased $
      indices-to-lams is $ Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
        App (App (indices-to-apps is $ mvar Y1ₓ) Erased $ App (indices-to-apps is $
            App (AppTp (AppTp (mvar $ mendler-names.cast ns) $ mtpvar Rₓ) $
              TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ)
               Erased $ mvar c2ₓ) NotErased $ mvar yₓ) NotErased $
          App (indices-to-apps is $ mvar ihₓ) NotErased $ mvar yₓ) NotErased $ mvar rₓ

  MendlerInd = DefTerm posinfo-gen (mendler-names.MendlerInd ns) NoType $
    Lam posinfo-gen Erased posinfo-gen Fₓ (SomeClass $ Tkk $ KndArrow k k) $
    Lam posinfo-gen Erased posinfo-gen fmapₓ
      (SomeClass $ Tkt $ TpApp (mtpvar $ mendler-names.Functor ns) $ mtpvar Fₓ) $
    indices-to-lams is $
    Lam posinfo-gen NotErased posinfo-gen fₓ (SomeClass $ Tkt $ indices-to-tpapps is $
      TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
    Lam posinfo-gen Erased posinfo-gen Qₓ (SomeClass $ Tkk $ indices-to-kind is $
      KndTpArrow (indices-to-tpapps is $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $
        mtpvar Fₓ) $ mvar fmapₓ) star) $
    Lam posinfo-gen NotErased posinfo-gen qₓ
      (SomeClass $ Tkt $ TpAppt (TpApp (TpApp (TpAppt (TpApp
        (mtpvar $ mendler-names.PrfAlgM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
        TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $
        mtpvar Qₓ) $ App (AppTp (mvar $ mendler-names.inFixIndM ns) $ mtpvar Fₓ) Erased $
        mvar fmapₓ) $
    App (App (indices-to-apps is $ AppTp (App (AppTp (mvar $ mendler-names.LiftProp1 ns) $
        mtpvar Fₓ) Erased $ mvar fmapₓ) $ mtpvar Qₓ) Erased $ mvar fₓ) NotErased $
      App (AppTp (IotaProj (mvar fₓ) "2" posinfo-gen) $ TpApp (TpAppt (TpApp
        (mtpvar $ mendler-names.LiftM ns) $ mtpvar Fₓ) $ mvar fmapₓ) $ mtpvar Qₓ) NotErased $
      App (App (App (App (App (App (AppTp (mvar $ mendler-names.convIH ns) $ mtpvar Fₓ)
        Erased $ mvar fmapₓ) NotErased $ (AppTp (App (AppTp
          (mvar $ mendler-names.LiftProp1 ns) $ mtpvar Fₓ) Erased $ mvar fmapₓ) $ mtpvar Qₓ))
        NotErased $ AppTp (App (AppTp (mvar $ mendler-names.LiftProp2 ns) $ mtpvar Fₓ) Erased
        $ mvar fmapₓ) $ mtpvar Qₓ) NotErased (AppTp (App (AppTp
        (mvar $ mendler-names.LiftProp3 ns) $ mtpvar Fₓ) Erased $ mvar fmapₓ) $ mtpvar Qₓ))
        NotErased (AppTp (App (AppTp (mvar $ mendler-names.LiftProp4 ns) $ mtpvar Fₓ) Erased
        $ mvar fmapₓ) $ mtpvar Qₓ)) NotErased $ mvar qₓ

  type-functor = DefType posinfo-gen (mendler-names.F ns)
    (parameters-to-kind ps $ KndArrow k k) $
    parameters-to-tplams ps $
    TpLambda posinfo-gen posinfo-gen x (Tkk $ k) $
    indices-to-tplams is $
    Iota posinfo-gen posinfo-gen yₓ Top-type $
    Abs posinfo-gen Erased posinfo-gen Xₓ
      (Tkk $ KndTpArrow Top-type $ indices-to-kind is star) $
    foldr
      (λ c → Abs posinfo-gen NotErased posinfo-gen ignored-var $ Tkt $ mk-ctr-type
        (ctxt-var-decl' yₓ $ ctxt-var-decl' Xₓ Γ) c Xₓ cs)
      (indices-to-tpapps is $ TpAppt (mtpvar Xₓ) (mvar yₓ)) cs

  eta-expand-fmaph-type : ctxt → var → type → term
  eta-expand-fmaph-type Γ x' T with decompose-ctr-type Γ T
  ...| Tₕ , ps , as with add-ps-to-ctxt Γ ps
  ...| Γ' =
    parameters-to-lams' ps $
    -- TODO: we can't give the user a recursive value for this!
    flip mapp (parameters-to-apps ps $ mvar x') $
    recompose-apps as $
    flip mappe (mvar cₓ) $
    flip AppTp (mtpvar Bₓ) $
    AppTp (mvar $ mendler-names.cast ns) (mtpvar Aₓ)

  eta-expand-fmap : ctr → term
  eta-expand-fmap (Ctr x' T) with ctxt-var-decl' Aₓ $ ctxt-var-decl' Bₓ $ ctxt-var-decl' cₓ Γ
  ...| Γ' with decompose-ctr-type Γ' T
  ...| Tₕ , ps , as with foldr (λ {(Decl _ _ _ x'' _ _) → ctxt-var-decl' x''}) Γ' ps
  ...| Γ'' =
    parameters-to-lams' ps $
    foldl (λ {(Decl pi pi' me x'' (Tkt T) pi'') t →
                App t me $
                if ~ is-free-in tt x T
                  then mvar x''
                  else eta-expand-fmaph-type Γ'' x'' T;
              (Decl pi pi' me x'' (Tkk k) pi'') t → AppTp t $ mtpvar x''})
          (mvar x') $ ps
  
  type-fmap = DefTerm posinfo-gen (mendler-names.fmap ns)
    (SomeType $ parameters-to-alls ps $ TpApp (mtpvar $ mendler-names.Functor ns) $
      parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $
    parameters-to-lams ps $
    Lam posinfo-gen Erased posinfo-gen Aₓ NoClass $
    Lam posinfo-gen Erased posinfo-gen Bₓ NoClass $
    Lam posinfo-gen Erased posinfo-gen cₓ NoClass $
    IotaPair posinfo-gen
      (indices-to-lams is $
       Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
       IotaPair posinfo-gen (IotaProj (mvar yₓ) "1" posinfo-gen)
         (Lam posinfo-gen Erased posinfo-gen Xₓ NoClass $
          constructors-to-lams' cs $
          foldl
            (flip mapp ∘ eta-expand-fmap)
            (AppTp (IotaProj (mvar yₓ) "2" posinfo-gen) $ mtpvar Xₓ) cs)
         NoGuide posinfo-gen)
      (Beta posinfo-gen NoTerm NoTerm) NoGuide posinfo-gen

  type-actual = DefType posinfo-gen x (parameters-to-kind ps $ k) $
    parameters-to-tplams ps $
    TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $
        parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $
      parameters-to-apps ps $ mvar $ mendler-names.fmap ns

  mk-ind-ctr-step-typeh : decl → type → type
  mk-ind-ctr-step-typeh (Decl pi pi' me x'' (Tkt T) pi'') with decompose-tpapps T
  ...| TpVar _ xₕ , as =
    if ~ xₕ =string x
      then id
      else (flip TpArrow NotErased $ flip TpAppt (mvar x'') $
             curry recompose-tpapps (mtpvar Qₓ) $ take (length as ∸ length ps) as)
  ...| _ = id
  mk-ind-ctr-step-typeh _ = id

  mk-ind-ctr-step-type : ctxt → ctr → type
  mk-ind-ctr-step-type Γ (Ctr x' T) with
    decompose-ctr-type Γ $ subst-type Γ (parameters-to-tpapps ps $ mtpvar x) x T
  ...| Tₕ , ps' , as =
    parameters-to-alls ps' $
    foldr mk-ind-ctr-step-typeh
      (TpAppt (curry recompose-tpapps (mtpvar Qₓ) $ take (length as ∸ length ps) as) $
        parameters-to-apps ps' $ parameters-to-apps ps $ mvar x') ps'

  type-ind-ctr-cast : decl → term → term
  type-ind-ctr-cast (Decl pi pi' me x' (Tkk k) pi'') t = AppTp t $ mtpvar x'
  type-ind-ctr-cast (Decl pi pi' me x' (Tkt T) pi'') t with decompose-tpapps T
  ...| TpVar _ xₕ , as = App t me $
    if xₕ =string x
      then mapp (recompose-apps as $ mappe (AppTp (AppTp (mvar $ mendler-names.cast ns) $ mtpvar Rₓ) $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ parameters-to-apps ps $ mvar $ mendler-names.fmap ns) $ mvar cₓ) (mvar x')
      else mvar x'
  ...| _ = App t me $ mvar x'

  type-ind-ctr-step : decl → term → term
  type-ind-ctr-step (Decl pi pi' me x' (Tkk k) pi'') t = t
  type-ind-ctr-step (Decl pi pi' me x' (Tkt T) pi'') t with decompose-tpapps T
  ...| TpVar _ xₕ , as =
    if xₕ =string x
      then mapp t (mapp (recompose-apps as $ mvar ihₓ) $ mvar x')
      else t
  ...| _ = t

  type-ind-ctr : ctr → term
  type-ind-ctr (Ctr x' T) with
    ctxt-var-decl' yₓ $
    ctxt-var-decl' Qₓ $
    ctxt-var-decl' Rₓ $
    ctxt-var-decl' cₓ $
    ctxt-var-decl' ihₓ Γ
  ...| Γ' with decompose-ctr-type Γ' T
  ...| Tₕ , ps' , as =
    parameters-to-lams' ps' $
    let Γ'' = add-ps-to-ctxt Γ' ps' in
    rename "x" from Γ'' for λ xₓ →
    rename "e" from Γ'' for λ eₓ →
    Lam posinfo-gen Erased posinfo-gen xₓ NoClass $
    Lam posinfo-gen Erased posinfo-gen eₓ NoClass $
    foldl type-ind-ctr-step (foldl type-ind-ctr-cast (mvar x') ps')  ps'

  type-ind = DefTerm posinfo-gen (mendler-names.Ind ns) NoType $
    parameters-to-lams ps $
    indices-to-lams is $
    Lam posinfo-gen NotErased posinfo-gen yₓ (SomeClass $ Tkt $
      indices-to-tpapps is $ parameters-to-tpapps ps $ mtpvar x) $
    Lam posinfo-gen Erased posinfo-gen Qₓ
      (SomeClass $ Tkk $ indices-to-kind is $
        KndTpArrow (indices-to-tpapps is $ parameters-to-tpapps ps $ mtpvar x) star) $
    -- constructors-to-lams (ctxt-var-decl' yₓ $ ctxt-var-decl' Qₓ Γ) x ps cs $
    flip (foldr λ {(Ctr x' T) → Lam posinfo-gen NotErased posinfo-gen x' (SomeClass $ Tkt $
      mk-ind-ctr-step-type (ctxt-var-decl' yₓ $ ctxt-var-decl' Qₓ Γ) $ Ctr x' T)}) cs $
    mapp (AppTp (mapp (indices-to-apps is $ mappe (AppTp (mvar $ mendler-names.MendlerInd ns)
        $ parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ parameters-to-apps ps $
      mvar $ mendler-names.fmap ns) $ mvar yₓ) $ mtpvar Qₓ) $
    Lam posinfo-gen Erased posinfo-gen Rₓ NoClass $
    Lam posinfo-gen Erased posinfo-gen cₓ NoClass $
    Lam posinfo-gen NotErased posinfo-gen ihₓ NoClass $
    indices-to-lams is $
    Lam posinfo-gen NotErased posinfo-gen yₓ NoClass $
    mappe (mappe
      (foldl (flip mapp ∘ type-ind-ctr)
        (AppTp (IotaProj (mvar yₓ) "2" posinfo-gen) $
          TpLambda posinfo-gen posinfo-gen yₓ (Tkt Top-type) $
          indices-to-tplams is $
          Abs posinfo-gen Erased posinfo-gen zₓ (Tkt $ indices-to-tpapps is $
            TpApp (parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ mtpvar Rₓ) $
          Abs posinfo-gen Erased posinfo-gen eₓ (Tkt $ mtpeq (mvar zₓ) $ mvar yₓ) $
          TpAppt (indices-to-tpapps is $ mtpvar Qₓ) $
          mapp (indices-to-apps is $ mappe (AppTp (mvar $ mendler-names.inFixIndM ns) $
            parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ parameters-to-apps ps $
            mvar $ mendler-names.fmap ns) $
            mapp (indices-to-apps is $ mappe (AppTp (AppTp (mvar $ mendler-names.cast ns) $ TpApp (parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ mtpvar Rₓ) $ TpApp (parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ parameters-to-apps ps $ mvar $ mendler-names.fmap ns) $ mappe (AppTp (AppTp (parameters-to-apps ps $ mvar $ mendler-names.fmap ns) $ mtpvar Rₓ) $ (TpAppt (TpApp (mtpvar $ mendler-names.FixIndM ns) $ parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $ parameters-to-apps ps $ mvar $ mendler-names.fmap ns)) $ mvar cₓ) $
            Phi posinfo-gen (mvar eₓ) (mvar zₓ) (mvar yₓ) posinfo-gen) cs)
      (mvar yₓ)) $ Beta posinfo-gen NoTerm NoTerm

  type-ctr-def : ctr → defTermOrType
  type-ctr-def (Ctr x' T) with
    decompose-ctr-type Γ (subst-type Γ (parameters-to-tpapps ps $ mtpvar x) x T)
  ...| Tₕ , ps' , as' = DefTerm posinfo-gen x' NoType $
    parameters-to-lams ps $
    parameters-to-lams ps' $
    mapp (recompose-apps (take (length as' ∸ length ps) as') $
          mappe (AppTp (mvar $ mendler-names.inFixIndM ns) $
            parameters-to-tpapps ps $ mtpvar $ mendler-names.F ns) $
      parameters-to-apps ps $ mvar $ mendler-names.fmap ns) $
    let Γ' = add-ps-to-ctxt Γ ps'
        Xₓ = rename Xₓ from Γ' for id in
    IotaPair posinfo-gen
      (mk-ctr-untyped-beta Γ' x' cs ps')
      (Lam posinfo-gen Erased posinfo-gen Xₓ NoClass $
       constructors-to-lams' cs $
       parameters-to-apps ps' $
       mvar x')
      NoGuide posinfo-gen

  type-ctrs-ind = foldr (csn ∘ type-ctr-def) (csn type-ind CmdsStart) cs

File-to-string : ctxt → cmds → tagged-val
File-to-string Γ = strRunTag "" Γ ∘ h where
  h : cmds → strM
  h CmdsStart = strEmpty
  h (CmdsNext (DefTermOrType op (DefTerm pi x (SomeType T) t) pi') cs) =
    strAdd x ≫str strAdd " ◂ " ≫str to-stringh T ≫str strAdd " = " ≫str to-stringh t ≫str strAdd ".\\n" ≫str h cs
  h (CmdsNext (DefTermOrType op (DefTerm pi x NoType t) pi') cs) =
    strAdd x ≫str strAdd " = " ≫str to-stringh t ≫str strAdd ".\\n" ≫str h cs
  h (CmdsNext (DefTermOrType op (DefType pi x k T) pi') cs) =
    strAdd x ≫str strAdd " ◂ " ≫str to-stringh k ≫str strAdd " = " ≫str to-stringh T ≫str strAdd ".\\n" ≫str h cs
  h (CmdsNext _ cs) = h cs
