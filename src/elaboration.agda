import cedille-options
module elaboration (options : cedille-options.options) where
open import lib
open import general-util
open import cedille-types
open import classify options {Id}
open import ctxt
open import conversion
open import meta-vars options {Id}
open import subst
open import syntax-util
open import toplevel-state options {IO} -- main imports toplevel-state with IO
open import to-string options
open import rename
open import rewriting

-- Unimplemented expressions: Lft, NoSpans, Hole
-- TODO: Module parameters and arguments

private
  
  {- Helpers -}
  
  infixl 2 _≫=maybec_

  _≫=maybec_ : ∀ {A B C : Set} → maybe (A × B) → (A → B → maybe C) → maybe C
  _≫=maybec_ m f = m ≫=maybe uncurry f
  
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

  subst : ∀ {ed ed' : exprd} → ctxt → ⟦ ed' ⟧ → var → ⟦ ed ⟧ → ⟦ ed ⟧
  subst{TERM} = subst-term
  subst{TYPE} = subst-type
  subst{KIND} = subst-kind
  subst Γ _ _ x = x

  renamectxt-single : var → var → renamectxt
  renamectxt-single = renamectxt-insert empty-renamectxt

  rename-var : ∀ {ed : exprd} → ctxt → var → var → 𝔹 → ⟦ ed ⟧ → ⟦ ed ⟧
  rename-var {TERM} Γ x x' tt = substh-term {TERM} Γ (renamectxt-single x x') (trie-single x (Var posinfo-gen x'))
  rename-var {TYPE} Γ x x' ff = substh-type {TYPE} Γ (renamectxt-single x x') (trie-single x (TpVar posinfo-gen x'))
  rename-var {KIND} Γ x x' tt = substh-kind {TERM} Γ (renamectxt-single x x') (trie-single x (Var posinfo-gen x'))
  rename-var {TERM} Γ x x' ff = substh-term {TYPE} Γ (renamectxt-single x x') (trie-single x (TpVar posinfo-gen x'))
  rename-var {TYPE} Γ x x' tt = substh-type {TERM} Γ (renamectxt-single x x') (trie-single x (Var posinfo-gen x'))
  rename-var {KIND} Γ x x' ff = substh-kind {TYPE} Γ (renamectxt-single x x') (trie-single x (TpVar posinfo-gen x'))
  rename-var Γ x x' b t = t

  rename_from_for_ : ∀ {X : Set} → var → ctxt → (var → X) → X
  rename "_" from Γ for f = f "_"
  rename x from Γ for f = f (fresh-var x (ctxt-binds-var Γ) empty-renamectxt)
  
  fresh-id-term : ctxt → term
  fresh-id-term Γ =
    rename "x" from Γ for λ x →
    Lam posinfo-gen KeptLambda posinfo-gen x NoClass (Var posinfo-gen x)

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
elab-hnf-type : ctxt → type → 𝔹 → maybe type
elab-app-term : ctxt → term → maybe ((meta-vars → maybe term) × type × meta-vars)

elab-type Γ T = elab-typeh Γ T tt
elab-kind Γ k = elab-kindh Γ k tt
elab-tk Γ atk = elab-tkh Γ atk tt
elab-pure-type Γ T = maybe-map fst (elab-typeh Γ T ff)
elab-pure-kind Γ k = elab-kindh Γ k ff
elab-pure-tk Γ atk = elab-tkh Γ atk ff

elab-check-term Γ (App t me t') T =
  elab-app-term Γ (App t me t') ≫=maybe λ where
    (tf , T , Xs) → tf Xs
elab-check-term Γ (AppTp t T) T' =
  elab-app-term Γ (AppTp t T) ≫=maybe λ where
    (tf , T , Xs) → tf Xs
elab-check-term Γ (Beta pi ot ot') T =
  let ot'' = case ot' of λ where NoTerm → just (fresh-id-term Γ); (SomeTerm t _) → elab-pure-term Γ (erase-term t) in
  case ot of λ where
    NoTerm → elab-hnf-type Γ T tt ≫=maybe λ where
      (TpEq _ t₁ t₂ _) →
        ot'' ≫=maybe λ t →
        just (Beta posinfo-gen (SomeTerm t₁ posinfo-gen) (SomeTerm t posinfo-gen))
      _ → nothing
    (SomeTerm t _) →
      elab-pure-term Γ (erase-term t) ≫=maybe λ t →
      ot'' ≫=maybe λ t' →
      just (Beta posinfo-gen (SomeTerm t posinfo-gen) (SomeTerm t' posinfo-gen))
elab-check-term Γ (Chi pi mT t) T = case mT of λ where
  NoAtype → maybe-map fst (elab-synth-term Γ t)
  (Atype T') →
    elab-pure-type Γ (erase-type T') ≫=maybe λ T' →
    elab-check-term Γ t T' ≫=maybe λ t →
    just (Rho posinfo-gen RhoPlain NoNums t (Guide posinfo-gen "_" T') t)
elab-check-term Γ (Delta pi mT t) T =
  elab-pure-type Γ (erase-type T) ≫=maybe λ T →
  elab-check-term Γ t delta-contra ≫=maybe λ t →
  just (Delta posinfo-gen (Atype T) t)
elab-check-term Γ (Epsilon pi lr mm t) T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (TpEq _ t₁ t₂ _) → elab-check-term Γ (Chi posinfo-gen
      (Atype (check-term-update-eq Γ lr mm posinfo-gen t₁ t₂ posinfo-gen)) t) T
    _ → nothing
elab-check-term Γ (Hole pi) T = nothing
elab-check-term Γ (IotaPair pi t t' og pi') T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (Iota _ pi x T' T'') →
      elab-check-term Γ t T' ≫=maybe λ t →
      elab-check-term Γ t' (subst Γ t x T'') ≫=maybe λ t' →
      just (IotaPair posinfo-gen t t' (Guide pi x T'') posinfo-gen)
    _ → nothing
elab-check-term Γ (IotaProj t n pi) T =
  elab-synth-term Γ t ≫=maybec λ t T' →
  just (IotaProj t n posinfo-gen)
elab-check-term Γ (Lam pi l pi' x oc t) T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (Abs _ b pi'' x' atk T') →
      rename x from Γ for λ x'' →
      elab-check-term (ctxt-tk-decl' pi' x'' atk Γ) (rename-var Γ x x'' (tk-is-type atk) t)
        (rename-var Γ x' x'' (tk-is-type atk) T') ≫=maybe λ t →
      just (Lam posinfo-gen l pi' x (SomeClass atk) t)
    _ → nothing
elab-check-term Γ (Let pi d t) T =
  case d of λ where
  (DefTerm pi' x NoCheckType t') →
    elab-synth-term Γ t' ≫=maybec λ t' T →
    elab-check-term Γ (subst Γ t' x t) T
  (DefTerm pi' x (Type T') t') →
    elab-check-term Γ t' T' ≫=maybe λ t' →
    elab-check-term Γ (subst Γ t' x t) T
  (DefType pi' x k T') →
    elab-type Γ T' ≫=maybec λ T' k' →
    elab-check-term Γ (subst Γ T' x t) T
elab-check-term Γ (Parens pi t pi') T = elab-check-term Γ t T
elab-check-term Γ (Phi pi t t₁ t₂ pi') T =
  elab-check-term Γ t₁ T ≫=maybe λ t₁ →
  elab-pure-term Γ (erase-term t₂) ≫=maybe λ t₂ →
  elab-check-term Γ t (TpEq posinfo-gen (erase-term t₁) t₂ posinfo-gen) ≫=maybe λ t →
  just (Phi posinfo-gen t t₁ t₂ posinfo-gen)
elab-check-term Γ (Rho pi op on t og t') T =
  elab-synth-term Γ t ≫=maybec λ t T' →
  elab-hnf-type Γ (erase-type T') ff ≫=maybe λ where
    (TpEq _ t₁ t₂ _) → case og of λ where
      NoGuide →
        elab-pure-type Γ (erase-type T) ≫=maybe λ T →
        rename "x" from Γ for λ x →
        let ns = fst (optNums-to-stringset on)
            rT = fst (rewrite-type T Γ empty-renamectxt (is-rho-plus op) ns t₁ (Var posinfo-gen x) 0)
            rT' = subst Γ t₂ x rT in
        elab-check-term Γ t' rT' ≫=maybe λ t' →
        just (Rho posinfo-gen RhoPlain NoNums (Sigma posinfo-gen t) (Guide posinfo-gen x rT) t')
      (Guide pi' x T') →
        elab-pure-type Γ (erase-type T') ≫=maybe λ T' →
        elab-check-term Γ t' (subst Γ t₂ x T') ≫=maybe λ t' →
        just (Rho posinfo-gen RhoPlain NoNums t (Guide pi' x T') t')
    _ → nothing
elab-check-term Γ (Sigma pi t) T =
  elab-hnf-type Γ T tt ≫=maybe λ where
    (TpEq _ t₁ t₂ _) →
      elab-check-term Γ t (TpEq posinfo-gen t₂ t₁ posinfo-gen) ≫=maybe λ t →
      just (Sigma posinfo-gen t)
    _ → nothing
elab-check-term Γ (Theta pi θ t ts) T =
  elab-synth-term Γ t ≫=maybec λ t T' →
  let x = case t of λ {(Var _ x) → x; _ → "_"} in
  rename x from Γ for λ x' →
  motive x x' T T' θ ≫=maybe λ mtv →
  elab-check-term Γ (App* (AppTp t mtv) (lterms-to-𝕃 θ ts)) T where
  wrap-var : var → type → maybe type
  wrap-var x T =
    rename x from Γ for λ x' →
    env-lookup Γ x ≫=maybe λ where
      (term-decl T' , loc) → just
        (TpLambda posinfo-gen posinfo-gen x' (Tkt T') (rename-var Γ x x' tt T))
      (type-decl k , loc) → just
        (TpLambda posinfo-gen posinfo-gen x' (Tkk k) (rename-var Γ x x' ff T))
      (term-def ps t T' , loc) → just
        (TpLambda posinfo-gen posinfo-gen x' (Tkt T') (rename-var Γ x x' tt T))
      (type-def ps T' k , loc) → just
        (TpLambda posinfo-gen posinfo-gen x' (Tkk k) (rename-var Γ x x' ff T))
      _ → nothing
  wrap-vars : vars → type → maybe type
  wrap-vars (VarsStart x) T = wrap-var x  T
  wrap-vars (VarsNext x xs) T = wrap-vars xs T ≫=maybe wrap-var x
  motive : var → var → type → type → theta → maybe type
  motive x x' T T' Abstract = just
    (TpLambda posinfo-gen posinfo-gen x' (Tkt T') (rename-var Γ x x' tt T))
  motive x x' T T' AbstractEq = just
    (TpLambda posinfo-gen posinfo-gen x' (Tkt T')
      (TpArrow (TpEq posinfo-gen t (Var posinfo-gen x') posinfo-gen) UnerasedArrow
               (rename-var Γ x x' tt T)))
  motive x x' T T' (AbstractVars vs) = wrap-vars vs T
elab-check-term Γ (Var pi x) T = just (Var posinfo-gen x)

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
      just (Beta posinfo-gen (SomeTerm t posinfo-gen) (SomeTerm t' posinfo-gen) ,
            TpEq posinfo-gen t t posinfo-gen)
    NoTerm → nothing
elab-synth-term Γ (Chi pi mT t) = case mT of λ where
  NoAtype → elab-synth-term Γ t
  (Atype T') →
    let id = fresh-id-term Γ
        β = Beta posinfo-gen (SomeTerm id posinfo-gen) (SomeTerm id posinfo-gen) in
    elab-pure-type Γ (erase-type T') ≫=maybe λ T' →
    elab-check-term Γ t T' ≫=maybe λ t →
    just (Rho posinfo-gen RhoPlain NoNums β (Guide posinfo-gen "_" T') t , T')
elab-synth-term Γ (Delta pi mT t) = (case mT of λ where
  NoAtype → just compileFailType
  (Atype T) → elab-pure-type Γ (erase-type T)) ≫=maybe λ T →
  elab-check-term Γ t delta-contra ≫=maybe λ t →
  just (Delta posinfo-gen (Atype T) t , T)
elab-synth-term Γ (Epsilon pi lr mm t) =
  elab-synth-term Γ t ≫=maybec λ where
    t (TpEq _ t₁ t₂ _) →
      let id = fresh-id-term Γ
          β = Beta posinfo-gen (SomeTerm id posinfo-gen) (SomeTerm id posinfo-gen)
          T = check-term-update-eq Γ lr mm posinfo-gen t₁ t₂ posinfo-gen in
      elab-pure-type Γ T ≫=maybe λ T →
      just (Rho posinfo-gen RhoPlain NoNums β (Guide posinfo-gen "_" T) t , T)
    _ _ → nothing
elab-synth-term Γ (Hole pi) = nothing
elab-synth-term Γ (IotaPair pi t₁ t₂ og pi') = case og of λ where
  NoGuide → nothing
  (Guide pi'' x T₂) →
    rename x from Γ for λ x' →
    elab-type (ctxt-var-decl pi'' x' Γ) (rename-var Γ x x' tt T₂) ≫=maybec λ T₂ k₂ →
    elab-synth-term Γ t₁ ≫=maybec λ t₁ T₁ →
    elab-check-term Γ t₂ (subst Γ t₁ x' T₂) ≫=maybe λ t₂ →
    just (IotaPair posinfo-gen t₁ t₂ (Guide pi'' x' T₂) posinfo-gen ,
          Iota posinfo-gen pi'' x' T₁ T₂)
elab-synth-term Γ (IotaProj t n pi) =
  elab-synth-term Γ t ≫=maybec λ where
    t (Iota _ pi' x T₁ T₂) →
      case n of λ where
        "1" → just (IotaProj t n posinfo-gen , T₁)
        "2" → just (IotaProj t n posinfo-gen , subst Γ t x T₂)
        _ → nothing
    _ _ → nothing
elab-synth-term Γ (Lam pi l pi' x oc t) = (case (l , oc) of λ where
  (ErasedLambda , SomeClass atk) → elab-tk Γ atk
  (KeptLambda , SomeClass (Tkt T)) → elab-tk Γ (Tkt T)
  _ → nothing) ≫=maybe λ atk →
  let b = case l of λ where KeptLambda → Pi; ErasedLambda → All in
  rename x from Γ for λ x' →
  elab-synth-term (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' (tk-is-type atk) t) ≫=maybec λ t T →
    just (Lam posinfo-gen l pi' x' (SomeClass atk) t , Abs posinfo-gen b pi' x' atk T)
elab-synth-term Γ (Let pi d t) = case d of λ where
  (DefTerm pi' x NoCheckType t') →
    elab-synth-term Γ t' ≫=maybec λ t' T →
    elab-synth-term Γ (subst Γ t' x t)
  (DefTerm pi' x (Type T) t') →
    elab-check-term Γ t' T ≫=maybe λ t' →
    elab-synth-term Γ (subst Γ t' x t)
  (DefType pi' x k T) →
    elab-type Γ T ≫=maybec λ T k' →
    elab-synth-term Γ (subst Γ T x t)
elab-synth-term Γ (Parens pi t pi') = elab-synth-term Γ t
elab-synth-term Γ (Phi pi t t₁ t₂ pi') =
  elab-synth-term Γ t₁ ≫=maybec λ t₁ T →
  elab-pure-term Γ (erase-term t₂) ≫=maybe λ t₂ →
  elab-check-term Γ t (TpEq posinfo-gen (erase-term t₁) t₂ posinfo-gen) ≫=maybe λ t →
  just (Phi posinfo-gen t t₁ t₂ posinfo-gen , T)
elab-synth-term Γ (Rho pi op on t og t') =
  elab-synth-term Γ t ≫=maybec λ t T →
  elab-synth-term Γ t' ≫=maybec λ t' T' →
  elab-hnf-type Γ (erase-type T) ff ≫=maybe λ where
    (TpEq _ t₁ t₂ _) → case og of λ where
      NoGuide →
        elab-pure-type Γ (erase-type T') ≫=maybe λ T' →
        rename "x" from Γ for λ x →
        let ns = fst (optNums-to-stringset on)
            rT = fst (rewrite-type T' Γ empty-renamectxt (is-rho-plus op) ns t₁ (Var posinfo-gen x) 0)
            rT' = subst Γ t₂ x rT in
        just (Rho posinfo-gen RhoPlain NoNums t (Guide posinfo-gen x rT) t' , rT')
      (Guide pi' x T') →
        elab-pure-type Γ (erase-type T') ≫=maybe λ T' →
        just (Rho posinfo-gen RhoPlain NoNums t (Guide pi' x T') t' ,
              subst Γ t₂ x T')
    _ → nothing
elab-synth-term Γ (Sigma pi t) =
  elab-synth-term Γ t ≫=maybec λ where
    t (TpEq _ t₁ t₂ _) → just (Sigma posinfo-gen t , TpEq posinfo-gen t₂ t₁ posinfo-gen)
    _ _ → nothing
elab-synth-term Γ (Theta pi θ t ts) = nothing
elab-synth-term Γ (Var pi x) =
  (env-lookup Γ x ≫=maybe λ where
    (term-decl T , loc) → just T
    (term-def ps t T , loc) → just T
    _ → nothing) ≫=maybe λ T →
  elab-hnf-type Γ T tt ≫=maybe λ T →
  just (Var posinfo-gen x , T)

elab-typeh Γ (Abs pi b pi' x atk T) b' =
  elab-tkh Γ atk b' ≫=maybe λ atk →
  rename x from Γ for λ x' →
  elab-typeh (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' (tk-is-type atk) T) b' ≫=maybec λ T k →
  just (Abs posinfo-gen b pi' x' atk T , Star posinfo-gen)
elab-typeh Γ (Iota pi pi' x T T') b =
  elab-typeh Γ T b ≫=maybec λ T k →
  rename x from Γ for λ x' →
  elab-typeh (ctxt-term-decl' pi' x' T Γ) (rename-var Γ x x' tt T') b ≫=maybec λ T' k' →
  just (Iota posinfo-gen pi' x' T T' , Star posinfo-gen)
elab-typeh Γ (Lft pi pi' x t lT) b = nothing
elab-typeh Γ (NoSpans T pi) b = nothing
elab-typeh Γ (TpApp T T') b =
  elab-typeh Γ T b ≫=maybec λ T k →
  elab-typeh Γ T' b ≫=maybec λ T' k' →
  case k of λ where
    (KndPi _ pi x (Tkk _) k'') → just (TpApp T T' , subst Γ T' x k'')
    _ → nothing
elab-typeh Γ (TpAppt T t) b =
  elab-typeh Γ T b ≫=maybec λ where
    T (KndPi _ pi x (Tkt T') k) →
      (if b then elab-check-term Γ t T' else elab-pure-term Γ (erase-term t)) ≫=maybe λ t →
      just (TpAppt T t , subst Γ t x k)
    _ _ → nothing
elab-typeh Γ (TpArrow T a T') b =
  elab-typeh Γ T b ≫=maybec λ T k →
  elab-typeh Γ T' b ≫=maybec λ T' k' →
  let b' = case a of λ where UnerasedArrow → Pi; ErasedArrow → All in
  just (Abs posinfo-gen b' posinfo-gen "_" (Tkt T) T' , Star posinfo-gen)
elab-typeh Γ (TpEq pi t t' pi') b =
  elab-pure-term Γ (erase-term t) ≫=maybe λ t →
  elab-pure-term Γ (erase-term t') ≫=maybe λ t' →
  just (TpEq posinfo-gen t t' posinfo-gen , Star posinfo-gen)
elab-typeh Γ (TpHole pi) b = nothing
elab-typeh Γ (TpLambda pi pi' x atk T) b =
  elab-tkh Γ atk b ≫=maybe λ atk →
  rename x from Γ for λ x' →
  elab-typeh (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' (tk-is-type atk) T) b ≫=maybec λ T k →
  just (TpLambda posinfo-gen pi' x' atk T , KndPi posinfo-gen pi' x' atk k)
elab-typeh Γ (TpParens pi T pi') b = elab-typeh Γ T b
elab-typeh Γ (TpVar pi x) b =
  (env-lookup Γ x ≫=maybe λ where
    (type-decl k , loc) → just k
    (type-def ps T k , loc) → just k
    _ → nothing) ≫=maybe λ k →
  elab-kindh Γ k b ≫=maybe λ k →
  just (TpVar posinfo-gen x , k)

elab-kindh Γ (KndArrow k k') b =
  elab-kindh Γ k b ≫=maybe λ k →
  elab-kindh Γ k' b ≫=maybe λ k' →
  just (KndPi posinfo-gen posinfo-gen "_" (Tkk k) k')
elab-kindh Γ (KndParens pi k pi') b = elab-kindh Γ k b
elab-kindh Γ (KndPi pi pi' x atk k) b =
  elab-tkh Γ atk b ≫=maybe λ atk →
  rename x from Γ for λ x' →
  elab-kindh (ctxt-tk-decl' pi' x' atk Γ) (rename-var Γ x x' (tk-is-type atk) k) b ≫=maybe λ k →
  just (KndPi posinfo-gen pi' x' atk k)
elab-kindh Γ (KndTpArrow T k) b =
  elab-typeh Γ T b ≫=maybec λ T _ →
  elab-kindh Γ k b ≫=maybe λ k →
  just (KndPi posinfo-gen posinfo-gen "_" (Tkt T) k)
elab-kindh Γ (KndVar pi x as) b =
  env-lookup-kind-var-qdef Γ x as ≫=maybec do-subst as
  where
  do-subst : args → params → kind → maybe kind
  do-subst (ArgsCons (TermArg t) ys) (ParamsCons (Decl _ _ x _ _) ps) k = do-subst ys ps (subst-kind Γ t x k)
  do-subst (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ x _ _) ps) k = do-subst ys ps (subst-kind Γ t x k)
  do-subst ArgsNil ParamsNil k = elab-kindh Γ k b
  do-subst _ _ _ = nothing
elab-kindh Γ (Star pi) b = just (Star posinfo-gen)

elab-tkh Γ (Tkt T) b = elab-typeh Γ T b ≫=maybec λ T _ → just (Tkt T)
elab-tkh Γ (Tkk k) b = maybe-map Tkk (elab-kindh Γ k b)

elab-pure-term Γ (Var pi x) = just (Var posinfo-gen x)
elab-pure-term Γ (App t NotErased t') = 
  elab-pure-term Γ t ≫=maybe λ t →
  elab-pure-term Γ t' ≫=maybe λ t' →
  just (App t NotErased t')
elab-pure-term Γ (Lam pi KeptLambda pi' x NoClass t) =
  rename x from Γ for λ x' →
  elab-pure-term (ctxt-var-decl pi x' Γ) (rename-var Γ x x' tt t) ≫=maybe λ t →
  just (Lam posinfo-gen KeptLambda pi' x' NoClass t)
elab-pure-term Γ (Let pi (DefTerm pi' x NoCheckType t) t') =
  elab-pure-term Γ t ≫=maybe λ t →
  elab-pure-term Γ (subst Γ t x t')
elab-pure-term _ _ = nothing -- should be erased

elab-hnf-type Γ T b =
  elab-typeh Γ (hnf Γ (unfolding-elab unfold-head) T tt) b ≫=maybec λ T k → just T

drop-meta-var : meta-vars → meta-vars
drop-meta-var Xs = record Xs {order = tail (meta-vars.order Xs)}

drop-meta-vars : meta-vars → ℕ → meta-vars
drop-meta-vars Xs zero = Xs
drop-meta-vars Xs (suc n) = drop-meta-vars (drop-meta-var Xs) n

elab-app-sols : ctxt → term → meta-vars → ℕ → maybe term
elab-app-sols Γ t Xs zero = just t
elab-app-sols Γ t Xs (suc n) =
  head2 (meta-vars.order Xs) ≫=maybe λ x →
  trie-lookup (meta-vars.varset Xs) x ≫=maybe λ X →
  case (meta-var.sol X) of λ where
    (meta-var-tm _ _) → nothing
    (meta-var-tp k mtp) →
      let id' = fresh-id-term Γ
          T = maybe-else (TpEq posinfo-gen id' id' posinfo-gen) id mtp in
      elab-type Γ T ≫=maybec λ T k →
      elab-app-sols Γ (AppTp t T) (drop-meta-var Xs) n

elab-app-term Γ (App t m t') =
  elab-app-term Γ t ≫=maybe λ {(t , T , Xs) →
  let abs-num = length (meta-vars.order Xs) in
  case meta-vars-unfold-tmapp Γ Xs T of λ where
    (_ , no-tp-arrow _) → nothing
    (Xs , yes-tp-arrow T' Tₐ m' cod) →
      let abs-num' = length (meta-vars.order Xs)
          num-apps = abs-num' ∸ abs-num
          ret t' cod' Xs = just ((λ Xs → t Xs ≫=maybe λ t → elab-app-sols Γ t (drop-meta-vars Xs abs-num) num-apps ≫=maybe λ t → just (App t m t')) , cod' , Xs) in
      case meta-vars-are-free-in-type Xs Tₐ of λ where
        ff → elab-check-term Γ t' Tₐ ≫=maybe λ t' →
             ret t' (cod t') Xs
        tt → elab-synth-term Γ t' ≫=maybec λ t' Tₐ' →
             case meta-vars-match Γ Xs empty-trie Tₐ Tₐ' of λ where
               (yes-error _) → nothing
               (no-error Xs) → ret t' (cod t') Xs}

elab-app-term Γ (AppTp t T) =
  elab-type Γ T ≫=maybec λ T _ →
  elab-app-term Γ t ≫=maybe λ {(t , Tₕ , Xs) →
  case meta-vars-unfold-tpapp Γ Xs Tₕ of λ where
    (no-tp-abs _) → nothing
    (yes-tp-abs _ b _ x k Tₕ') →
      let X = meta-vars-fresh-tp Xs x k (just T)
          Tₕ'' = rename-var Γ x (meta-var-name X) ff Tₕ' in
      just ((λ Xs → t Xs ≫=maybe λ t → just (AppTp t T)) , Tₕ'' , meta-vars-add Xs X)}

elab-app-term Γ (Parens pi t pi') = elab-app-term Γ t
elab-app-term Γ t =
  elab-synth-term Γ t ≫=maybec λ t T →
  just ((λ _ → just t) , T , meta-vars-empty)

{-# TERMINATING #-}
elab-file : toplevel-state → stringset → (filename : string) → maybe (rope × toplevel-state)
elab-cmds : toplevel-state → (string → maybe string) → stringset → cmds → maybe (rope × toplevel-state)

elab-cmds s lf ss CmdsStart = just ([[]] , s)
elab-cmds s lf ss (CmdsNext (DefTermOrType (DefTerm pi x NoCheckType t) _) cs) =
  let Γ = toplevel-state.Γ s in
  elab-synth-term Γ (qualif-term Γ t) ≫=maybec λ t T →
  elab-cmds (record s {Γ = ctxt-term-def pi globalScope nonParamVar x t T Γ}) lf ss cs ≫=maybec λ r s →
  just ([[ "\n\n" ]] ⊹⊹ [[ x ]] ⊹⊹ [[ " = " ]] ⊹⊹ to-string Γ t ⊹⊹ [[ " . " ]] ⊹⊹ r , s)
elab-cmds s lf ss (CmdsNext (DefTermOrType (DefTerm pi x (Type T) t) _) cs) =
  let Γ = toplevel-state.Γ s in
  elab-hnf-type Γ (qualif-type Γ T) tt ≫=maybe λ T →
  elab-check-term Γ (qualif-term Γ t) T ≫=maybe λ t →
  elab-cmds (record s {Γ = ctxt-term-def pi globalScope nonParamVar x t T Γ}) lf ss cs ≫=maybec λ r s →
  just ([[ "\n\n" ]] ⊹⊹ [[ x ]] ⊹⊹ [[ " = " ]] ⊹⊹ to-string Γ t ⊹⊹ [[ " . " ]] ⊹⊹ r , s)
elab-cmds s lf ss (CmdsNext (DefTermOrType (DefType pi x _ T) _) cs) =
  let Γ = toplevel-state.Γ s in
  elab-type Γ (qualif-type Γ T) ≫=maybec λ T k →
  elab-cmds (record s {Γ = ctxt-type-def pi globalScope nonParamVar x T k Γ}) lf ss cs ≫=maybec λ r s →
      just ([[ "\n\n" ]] ⊹⊹ [[ x ]] ⊹⊹ [[ " ◂ " ]] ⊹⊹ to-string Γ k ⊹⊹ [[ " = " ]] ⊹⊹ to-string Γ T ⊹⊹ [[ " . " ]] ⊹⊹ r , s)
elab-cmds s lf ss (CmdsNext (DefKind pi x ps k pi') cs) =
  let Γ = toplevel-state.Γ s in
  elab-kind Γ (qualif-kind Γ k) ≫=maybe λ k →
  elab-cmds (record s {Γ = ctxt-kind-def pi x ps k Γ}) lf ss cs
elab-cmds s lf ss (CmdsNext (ImportCmd (Import pi pi' op filename oa as pi'')) cs) =
  lf filename ≫=maybe λ filename →
  elab-file s ss filename ≫=maybec λ r s →
  elab-cmds s lf (stringset-insert ss filename) cs ≫=maybec λ r s →
  just ([[ "import " ]] ⊹⊹ [[ filename ]] ⊹⊹ [[ " . " ]] ⊹⊹ r , s) -- TODO: filename/../.cedille/filename.cedc instead?

elab-file s ss filename with stringset-contains ss filename
...| tt = just ([[ "Error: file " ]] ⊹⊹ [[ filename ]] ⊹⊹ [[ " already elaborated! (this shouldn't happen)" ]] , s)
...| ff =
  get-include-elt-if s filename ≫=maybe λ ie →
  include-elt.ast ie ≫=maybe λ where
    (File _ is _ _ mn ps cs _) →
      let ss = stringset-insert ss filename
          lf = trie-lookup (include-elt.import-to-dep ie) in
      elab-cmds s lf ss (imps-to-cmds is) ≫=maybec λ r s →
      elab-cmds s lf ss cs ≫=maybec λ r' s →
      just ([[ "module " ]] ⊹⊹ [[ mn ]] ⊹⊹ [[ " . " ]] ⊹⊹ r' ⊹⊹ r , s)
