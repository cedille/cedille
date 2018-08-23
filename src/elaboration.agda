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
open import elaboration-helpers options
open import templates
import spans options' {id} as id-spans

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

private
  
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

private
  ie-set-span-ast : include-elt → ctxt → start → include-elt
  ie-set-span-ast ie Γ ast = record ie
    {ss = inj₁ (regular-spans nothing
      [ mk-span "" "" "" [ "" , strRun Γ (file-to-string ast) , [] ] nothing ])}

  ie-get-span-ast : include-elt → maybe rope
  ie-get-span-ast ie with include-elt.ss ie
  ...| inj₁ (regular-spans nothing (mk-span "" "" ""
         (("" , r , []) :: []) nothing :: [])) = just r
  ...| _ = nothing

elab-t : Set → Set
elab-t X = toplevel-state → (var-mapping file-mapping : renamectxt) → X →
  maybe (X × toplevel-state × renamectxt × renamectxt)

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

record encoded-datatype : Set where
  constructor mk-encoded-datatype
  field
    data-def : datatype
    data-functor : var
    data-fmap : var
    functor : var
    cast : var
    fixed-point : var
    in-fix : var
    induction-principle : var
  x  = case data-def of λ where (Data x ps is cs) → x
  ps = case data-def of λ where (Data x ps is cs) → ps
  is = case data-def of λ where (Data x ps is cs) → is
  cs = case data-def of λ where (Data x ps is cs) → cs

record datatype-encoding : Set where
  constructor mk-datatype-encoding
  field
    template : start
    functor : var
    cast : var
    fixed-point : var
    in-fix : var
    induction-principle : var

  mk-defs : ctxt → datatype → cmds × encoded-datatype
  mk-defs Γ' (Data x ps is cs) = append-cmds tcs
    (csn functor-cmd $ csn fmap-cmd $ csn type-cmd $ foldr (csn ∘ ctr-cmd) CmdsStart cs) ,
    record {
      data-def = Data x ps is cs;
      data-functor = data-functorₓ;
      data-fmap = data-fmapₓ;
      functor = functorₓ;
      cast = castₓ;
      fixed-point = fixed-pointₓ;
      in-fix = in-fixₓ;
      induction-principle = induction-principleₓ}
    where
    csn = CmdsNext ∘ flip (DefTermOrType OpacTrans) posinfo-gen
    k = indices-to-kind is $ Star posinfo-gen
    
    Γ = add-parameters-to-ctxt ps $ add-constructors-to-ctxt cs $ ctxt-var-decl' x Γ'
    
    tcs-ρ = reindex-file Γ is template
    tcs = fst tcs-ρ
    ρ' = snd tcs-ρ

    data-functorₓ = fresh-var (x ^ "F") (ctxt-binds-var Γ) ρ'
    data-fmapₓ = fresh-var (x ^ "Fmap") (ctxt-binds-var Γ) ρ'
    functorₓ = renamectxt-rep ρ' functor
    castₓ = renamectxt-rep ρ' cast
    fixed-pointₓ = renamectxt-rep ρ' fixed-point
    in-fixₓ = renamectxt-rep ρ' in-fix
    induction-principleₓ = renamectxt-rep ρ' induction-principle
    ρ = renamectxt-insert (renamectxt-insert ρ' (x ^ "F") data-functorₓ) (x ^ "Fmap") data-fmapₓ
    
    new-var : ∀ {ℓ} {X : Set ℓ} → var → (var → X) → X
    new-var x f = f $ fresh-var x (ctxt-binds-var $ add-indices-to-ctxt is Γ) ρ

    functor-cmd = DefType posinfo-gen data-functorₓ (parameters-to-kind ps $ KndArrow k k) $
      parameters-to-tplams ps $
      TpLambda posinfo-gen posinfo-gen x (Tkk $ k) $
      indices-to-tplams is $
      new-var "x" λ xₓ →
      Iota posinfo-gen posinfo-gen xₓ (mtpeq id-term id-term) $
      new-var "X" λ Xₓ →
      Abs posinfo-gen Erased posinfo-gen Xₓ
        (Tkk $ KndTpArrow (mtpeq id-term id-term) $ indices-to-kind is star) $
      foldr (λ c → flip TpArrow NotErased $ mk-ctr-type (ctxt-var-decl' Xₓ Γ) c Xₓ cs)
        (indices-to-tpapps is $ TpAppt (mtpvar Xₓ) (mvar xₓ)) cs
    
    fmap-cmd : defTermOrType
    fmap-cmd with new-var "A" id | new-var "B" id | new-var "c" id
    ...| Aₓ | Bₓ | cₓ = DefTerm posinfo-gen data-fmapₓ (SomeType $
        parameters-to-alls ps $
        TpApp (mtpvar functorₓ) $
        parameters-to-tpapps ps $
        mtpvar data-functorₓ) $
      parameters-to-lams ps $
      Mlam Aₓ $ Mlam Bₓ $ Mlam cₓ $
      IotaPair posinfo-gen
        (indices-to-lams is $
         new-var "x" λ xₓ → mlam xₓ $
         IotaPair posinfo-gen (IotaProj (mvar xₓ) "1" posinfo-gen)
           (new-var "X" λ Xₓ → Mlam Xₓ $
             constructors-to-lams' cs $
             foldl
               (flip mapp ∘ eta-expand-fmap)
               (AppTp (IotaProj (mvar xₓ) "2" posinfo-gen) $ mtpvar Xₓ) cs)
          NoGuide posinfo-gen)
        (Beta posinfo-gen NoTerm NoTerm) NoGuide posinfo-gen
      where
      eta-expand-fmaph-type : ctxt → var → type → term
      eta-expand-fmaph-type Γ x' T with decompose-ctr-type Γ T
      ...| Tₕ , ps , as with add-parameters-to-ctxt ps Γ
      ...| Γ' =
        parameters-to-lams' ps $
        flip mapp (parameters-to-apps ps $ mvar x') $
        recompose-apps Erased as $
        flip mappe (mvar cₓ) $
        flip AppTp (mtpvar Bₓ) $
        AppTp (mvar castₓ) (mtpvar Aₓ)

      eta-expand-fmap : ctr → term
      eta-expand-fmap (Ctr x' T) with
        ctxt-var-decl' Aₓ $ ctxt-var-decl' Bₓ $ ctxt-var-decl' cₓ Γ
      ...| Γ' with decompose-ctr-type Γ' T
      ...| Tₕ , ps , as with foldr (λ {(Decl _ _ _ x'' _ _) → ctxt-var-decl' x''}) Γ' ps
      ...| Γ'' = parameters-to-lams' ps $ foldl
        (λ {(Decl pi pi' me x'' (Tkt T) pi'') t → App t me $
              if ~ is-free-in tt x T then mvar x'' else eta-expand-fmaph-type Γ'' x'' T;
            (Decl pi pi' me x'' (Tkk k) pi'') t → AppTp t $ mtpvar x''})
        (mvar x') $ ps

    type-cmd = DefType posinfo-gen x (parameters-to-kind ps $ k) $
      parameters-to-tplams ps $ TpAppt
        (TpApp (mtpvar fixed-pointₓ) $ parameters-to-tpapps ps $ mtpvar data-functorₓ)
        (parameters-to-apps ps $ mvar data-fmapₓ)

    ctr-cmd : ctr → defTermOrType
    ctr-cmd (Ctr x' T) with
        decompose-ctr-type Γ (subst-type Γ (parameters-to-tpapps ps $ mtpvar x) x T)
    ...| Tₕ , ps' , as' = DefTerm posinfo-gen x' NoType $
      parameters-to-lams ps $
      parameters-to-lams ps' $
      mapp (recompose-apps Erased (take (length as' ∸ length ps) as') $
            mappe (AppTp (mvar in-fixₓ) $
              parameters-to-tpapps ps $ mtpvar data-functorₓ) $
        parameters-to-apps ps $ mvar data-fmapₓ) $
      let Γ' = add-parameters-to-ctxt ps' Γ
          Xₓ = rename "X" from Γ' for id in
      IotaPair posinfo-gen
        (mk-ctr-untyped-beta Γ' x' cs ps')
        (Mlam Xₓ $
         constructors-to-lams' cs $
         parameters-to-apps ps' $
         mvar x')
        NoGuide posinfo-gen


mendler-encoding : datatype-encoding
mendler-encoding = record {
  template = MendlerTemplate;
  functor = "Functor";
  cast = "cast";
  fixed-point = "CVFixIndM";
  in-fix = "cvInFixIndM";
  induction-principle = "cvIndFixIndM"}

mendler-simple-encoding : datatype-encoding
mendler-simple-encoding = record {
  template = MendlerSimpleTemplate;
  functor = "RecFunctor";
  cast = "cast";
  fixed-point = "FixM";
  in-fix = "inFix";
  induction-principle = "IndFixM"}
