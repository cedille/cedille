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


{- Datatypes -}

mendler-encoding : datatype-encoding
mendler-encoding =
  let functorₓ = "Functor"
      castₓ = "cast"
      fixpoint-typeₓ = "CVFixIndM"
      fixpoint-inₓ = "cvInFixIndM"
      fixpoint-indₓ = "cvIndFixIndM" in
  record {
    template = MendlerTemplate;
    functor = functorₓ;
    cast = castₓ;
    fixpoint-type = fixpoint-typeₓ;
    fixpoint-in = fixpoint-inₓ;
    fixpoint-ind = fixpoint-indₓ;
    elab-mu = λ {
      (Data x ps is cs)
      (mk-encoded-datatype-names data-functorₓ data-fmapₓ data-functor-indₓ castₓ
        fixpoint-typeₓ fixpoint-inₓ fixpoint-indₓ)
      Γ t oT ms → record {
        elab-check-mu = λ ihₓ T → nothing;
        elab-synth-mu = case oT of λ {
          NoType ihₓ → nothing;
          (SomeType Tₘ) ihₓ → nothing
        };
      
        elab-check-mu' = λ T → nothing;
        elab-synth-mu' = case oT of λ {
          NoType → nothing;
          (SomeType Tₘ) → nothing
        }
      }
    }
  }

mendler-simple-encoding : datatype-encoding
mendler-simple-encoding =
  let functorₓ = "RecFunctor"
      castₓ = "cast"
      fixpoint-typeₓ = "FixM"
      fixpoint-inₓ = "inFix"
      fixpoint-indₓ = "IndFixM" in
  record {
    template = MendlerSimpleTemplate;
    functor = functorₓ;
    cast = castₓ;
    fixpoint-type = fixpoint-typeₓ;
    fixpoint-in = fixpoint-inₓ;
    fixpoint-ind = fixpoint-indₓ;
    elab-mu = λ {
      (Data x ps is cs)
      (mk-encoded-datatype-names data-functorₓ data-fmapₓ data-functor-indₓ castₓ
        fixpoint-typeₓ fixpoint-inₓ fixpoint-indₓ)
      Γ t oT ms → record {
        elab-check-mu = λ ihₓ T →
          -- let Tₘ = case oT of λ {(SomeType Tₘ) → Tₘ; NoType → indices-to-tplams is $ TpLambda posinfo-gen posinfo-gen ignored-var (Tkt {!!}) T} in
          nothing;
        elab-synth-mu = case oT of λ {
          NoType ihₓ → nothing;
          (SomeType Tₘ) ihₓ → nothing
        };
      
        elab-check-mu' = λ T → nothing;
        elab-synth-mu' = case oT of λ {
          NoType → nothing;
          (SomeType Tₘ) → nothing
        }
      }
    }
  }

selected-encoding = mendler-simple-encoding
-- TODO: ^ Add option so user can choose encoding ^




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
elab-app-term : ctxt → term → prototype → 𝔹 → maybe ((meta-vars → maybe term) × spine-data)

elab-type Γ T = elab-typeh Γ T tt
elab-kind Γ k = elab-kindh Γ k tt
elab-tk Γ atk = elab-tkh Γ atk tt
elab-pure-type Γ T = maybe-map fst (elab-typeh Γ T ff)
elab-pure-kind Γ k = elab-kindh Γ k ff
elab-pure-tk Γ atk = elab-tkh Γ atk ff

elab-type-arrow (Abs pi b pi' x atk T) = Abs pi b pi' x (elab-tk-arrow atk) (elab-type-arrow T)
elab-type-arrow (Iota pi pi' x T T') = Iota pi pi' x (elab-type-arrow T) (elab-type-arrow T')
elab-type-arrow (Lft pi pi' x t lT) = Lft pi pi' x t lT
elab-type-arrow (NoSpans T pi) = elab-type-arrow T
elab-type-arrow (TpLet pi (DefTerm pi' x NoType t) T') = TpLet pi (DefTerm pi x NoType t) (elab-type-arrow T')
elab-type-arrow (TpLet pi (DefTerm pi' x (SomeType T) t) T') = TpLet pi (DefTerm pi x (SomeType (elab-type-arrow T)) t) T'
elab-type-arrow (TpLet pi (DefType pi' x k T) T') = TpLet pi (DefType pi' x (elab-kind-arrow k) (elab-type-arrow T)) (elab-type-arrow T')
elab-type-arrow (TpApp T T') = TpApp (elab-type-arrow T) (elab-type-arrow T')
elab-type-arrow (TpAppt T t) = TpAppt (elab-type-arrow T) t
elab-type-arrow (TpArrow T a T') = Abs posinfo-gen a posinfo-gen "_" (Tkt (elab-type-arrow T)) (elab-type-arrow T')
elab-type-arrow (TpEq pi t t' pi') = TpEq pi (erase-term t) (erase-term t') pi'
elab-type-arrow (TpHole pi) = TpHole pi
elab-type-arrow (TpLambda pi pi' x atk T) = TpLambda pi pi' x (elab-tk-arrow atk) (elab-type-arrow T)
elab-type-arrow (TpParens pi T pi') = elab-type-arrow T
elab-type-arrow (TpVar pi x) = TpVar pi x

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
  elab-app-term Γ (App t me t') (proto-maybe (just T)) tt ≫=maybe uncurry λ where
    tf (mk-spine-data Xs T' _) → tf Xs
elab-check-term Γ (AppTp t T) T' =
  elab-synth-term Γ t ≫=maybe uncurry λ t T'' →
  elab-type Γ T ≫=maybe uncurry λ T k →
  just (AppTp t T)
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
  (elab-hnf-type Γ T tt ≫=maybe to-abs) ≫=maybe λ where
    (mk-abs b x' atk free T') →
      rename (if x =string "_" && free then x' else x) from Γ for λ x'' →
      elab-tk Γ atk ≫=maybe λ tk →
      elab-check-term (ctxt-tk-decl' pi' x'' atk Γ) (rename-var Γ x x'' t)
        (rename-var Γ x' x'' T') ≫=maybe λ t →
      just (Lam posinfo-gen l posinfo-gen x'' (SomeClass atk) t)
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
            Γ' = ctxt-var-decl x Γ
            rT = fst (rewrite-type T Γ' (is-rho-plus op) ns t t₁ x 0)
            rT' = post-rewrite Γ x t t₂ rT in
        elab-hnf-type Γ rT' tt ≫=maybe λ rT' →
        elab-check-term Γ t' rT' ≫=maybe
        (just ∘ mrho (Sigma posinfo-gen t) x (erase-type rT))
      (Guide pi' x T') →
        let Γ' = ctxt-var-decl x Γ in
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
elab-check-term Γ (Mu pi x t ot pi' cs pi'') T = nothing
elab-check-term Γ (Mu' pi t ot pi' cs pi'')  T = nothing

elab-synth-term Γ (App t me t') =
  elab-app-term  Γ (App t me t') (proto-maybe nothing) tt ≫=maybe uncurry λ where
    tf (mk-spine-data Xs T _) →
      tf Xs ≫=maybe λ t'' →
      elab-hnf-type Γ (meta-vars-subst-type' ff Γ Xs (decortype-to-type T)) tt ≫=maybe λ T →
      just (t'' , T)
elab-synth-term Γ (AppTp t T) =
  elab-synth-term Γ t ≫=maybe uncurry λ t T' →
  elab-hnf-type Γ T' tt ≫=maybe λ where
    (Abs _ _ _ x (Tkk k) T'') →
      elab-type Γ T ≫=maybe uncurry λ T k' →
        just (AppTp t T , subst Γ T x T'')
    _ → nothing
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
    elab-type (ctxt-var-decl x' Γ) (rename-var Γ x x' T₂) ≫=maybe uncurry λ T₂ k₂ →
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
              just (IotaProj t n posinfo-gen , subst Γ (IotaProj t "1" posinfo-gen) x T₂) -- , T₂)
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
            Γ' = ctxt-var-decl x Γ
            rT = fst (rewrite-type T' Γ' (is-rho-plus op) ns t t₁ x 0)
            rT' = post-rewrite Γ' x t t₂ rT in
        -- elab-hnf-type Γ rT' tt ≫=maybe λ rT' →
        just (mrho t x (erase-type rT) t' , rT')
      (Guide pi' x T'') →
        let Γ' = ctxt-var-decl x Γ in
        elab-pure-type Γ' (erase-type T'') ≫=maybe λ T'' →
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
elab-synth-term Γ (Mu pi x t ot pi' cs pi'') = nothing
elab-synth-term Γ (Mu' pi t ot pi' cs pi'')  = nothing

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
  do-subst (ArgsCons (TermArg _ t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = do-subst ys ps (subst Γ t x k)
  do-subst (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = do-subst ys ps (subst Γ t x k)
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
  elab-pure-term (ctxt-var-decl x' Γ) (rename-var Γ x x' t) ≫=maybe λ t →
  just (mlam x' t)
elab-pure-term Γ (Let pi (DefTerm pi' x NoType t) t') =
  elab-pure-term Γ t ≫=maybe λ t →
  elab-pure-term Γ (subst Γ t x t')
elab-pure-term _ _ = nothing -- should be erased

elab-app-term Γ (App t me t') pt max =
  elab-app-term Γ t (proto-arrow me pt) ff ≫=maybe uncurry λ where
    tf (mk-spine-data Xs dt locl) →
      case fst (meta-vars-unfold-tmapp' Γ ("" , "" , "") Xs dt Γ id-spans.empty-spans) of uncurry λ where
        Ys (not-tpabsd _) → nothing
        Ys (inj₂ arr) →
          elab-app-term' Xs Ys t t' arr (islocl locl) ≫=maybe uncurry λ where
            t' (check-term-app-return Xs' T₂ Tᵣ arg-mode) →
              fst (check-spine-locality Γ Xs' (decortype-to-type Tᵣ) max (pred locl) Γ id-spans.empty-spans) ≫=maybe uncurry' λ Xs'' locl' is-loc →
              just ((λ Xs → tf (if is-loc then Xs' else Xs) ≫=maybe λ t → fill-meta-vars t (if is-loc then Xs' else Xs) Ys ≫=maybe λ t → just (App t me t')) ,
                    mk-spine-data Xs'' Tᵣ locl')
  where
  islocl = (max ||_) ∘ (iszero ∘ pred)
  fill-meta-vars : term → meta-vars → 𝕃 meta-var → maybe term
  fill-meta-vars t Xs = flip foldl (just t) λ where
    (meta-var-mk x _ _) tₘ → tₘ ≫=maybe λ t → meta-vars-lookup Xs x ≫=maybe λ where
      (meta-var-mk _ (meta-var-tp k Tₘ) _) → Tₘ ≫=maybe λ T → just (AppTp t (meta-var-sol.sol T))
      (meta-var-mk _ (meta-var-tm T tₘ) _) → nothing

  elab-app-term' : (Xs : meta-vars) → (Ys : 𝕃 meta-var) → (t₁ t₂ : term) → is-tmabsd → 𝔹 → maybe (term × check-term-app-ret)
  elab-app-term' Xs Zs t₁ t₂ (mk-tmabsd dt me x dom occurs cod) is-locl =
    let Xs' = meta-vars-add* Xs Zs
        T = decortype-to-type dt in
    if ~ meta-vars-are-free-in-type Xs' dom
      then (elab-check-term Γ t₂ dom ≫=maybe λ t₂ →
            let rdt = fst $ subst-decortype Γ t₂ x cod Γ id-spans.empty-spans in
            just (t₂ , check-term-app-return Xs' dom (if occurs then rdt else cod) checking))
      else (elab-synth-term Γ t₂ ≫=maybe uncurry λ t₂ T₂ →
            case fst (match-types Xs' empty-trie match-unfolding-both dom T₂ Γ id-spans.empty-spans) of λ where
              (match-error _) → nothing
              (match-ok Xs) →
                let rdt = fst $ subst-decortype Γ t₂ x cod Γ id-spans.empty-spans
                    rdt' = fst $ meta-vars-subst-decortype Γ Xs (if occurs then rdt else cod) Γ id-spans.empty-spans in
                just (t₂ , check-term-app-return Xs T₂ rdt' synthesizing))

elab-app-term Γ (AppTp t T) pt max =
  elab-app-term Γ t pt max ≫=maybe uncurry λ where
    tf (mk-spine-data Xs dt locl) →
      let Tₕ = decortype-to-type dt in
      case fst (meta-vars-unfold-tpapp' Γ Xs dt Γ id-spans.empty-spans) of λ where
        (not-tpabsd _) → nothing
        (yes-tpabsd dt me x k sol rdt) →
          elab-type Γ T ≫=maybe uncurry λ T k' →
          just ((λ Xs → tf Xs ≫=maybe λ t → just (AppTp t T)) ,
            mk-spine-data Xs (fst $ subst-decortype Γ T x rdt Γ id-spans.empty-spans) locl)

elab-app-term Γ (Parens _ t _) pt max =
  elab-app-term Γ t pt max

elab-app-term Γ t pt max =
  elab-synth-term Γ t ≫=maybe uncurry λ t T →
  let locl = num-arrows-in-type Γ T
      ret = fst $ match-prototype meta-vars-empty ff T pt Γ id-spans.empty-spans
      dt = match-prototype-data.match-proto-dectp ret in
  just ((λ Xs → just t) , mk-spine-data meta-vars-empty dt locl)



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
elab-t X = toplevel-state → (var-mapping file-mapping : renamectxt) → trie encoded-datatype →
             X → maybe (X × toplevel-state × renamectxt × renamectxt × trie encoded-datatype)

{-# TERMINATING #-}
elab-file' : elab-t string
elab-cmds : elab-t cmds
elab-params : elab-t params
elab-args : elab-t (args × params)
elab-imports : elab-t imports

elab-params ts ρ φ μ ParamsNil = just (ParamsNil , ts , ρ , φ , μ)
elab-params ts ρ φ μ (ParamsCons (Decl _ pi me x atk _) ps) =
  let Γ = toplevel-state.Γ ts in
  elab-tk Γ (subst-qualif Γ ρ atk) ≫=maybe λ atk →
  rename x - x from ρ for λ x' ρ →
  elab-params (record ts {Γ = ctxt-param-decl x x' atk Γ}) ρ φ μ ps ≫=maybe uncurry λ ps ω →
  just (ParamsCons (Decl posinfo-gen posinfo-gen me x' atk posinfo-gen) ps , ω)

elab-args ts ρ φ μ (ArgsNil , ParamsNil) = just ((ArgsNil , ParamsNil) , ts , ρ , φ , μ)
elab-args ts ρ φ μ (_ , ParamsNil) = nothing -- Too many arguments
elab-args ts ρ φ μ (ArgsNil , ParamsCons p ps) = just ((ArgsNil , ParamsCons p ps) , ts , ρ , φ , μ)
elab-args ts ρ φ μ (ArgsCons a as , ParamsCons (Decl _ _ me x atk _) ps) =
  let Γ = toplevel-state.Γ ts in
  case (a , atk) of λ where
    (TermArg me' t , Tkt T) →
      elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
      elab-check-term Γ (subst-qualif Γ ρ t) T ≫=maybe λ t →
      rename qualif-new-var Γ x - x lookup ρ for λ x' ρ →
      let ts = record ts {Γ = ctxt-term-def' x x' t T OpacTrans Γ} in
      elab-args ts ρ φ μ (as , ps) ≫=maybe (uncurry ∘ uncurry) λ as ps ω →
      just ((ArgsCons (TermArg me' t) as , ParamsCons (Decl posinfo-gen posinfo-gen me x' (Tkt T) posinfo-gen) ps) , ω)
    (TypeArg T , Tkk _) →
      elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
      rename qualif-new-var Γ x - x lookup ρ for λ x' ρ →
      let ts = record ts {Γ = ctxt-type-def' x x' T k OpacTrans Γ} in
      elab-args ts ρ φ μ (as , ps) ≫=maybe (uncurry ∘ uncurry) λ as ps ω →
      just ((ArgsCons (TypeArg T) as , ParamsCons (Decl posinfo-gen posinfo-gen me x' (Tkk k) posinfo-gen) ps) , ω)
    _ → nothing

elab-imports ts ρ φ μ ImportsStart = just (ImportsStart , ts , ρ , φ , μ)
elab-imports ts ρ φ μ (ImportsNext (Import _ op _ ifn oa as _) is) =
  let Γ = toplevel-state.Γ ts
      fn = ctxt-get-current-filename Γ
      mod = ctxt-get-current-mod Γ in
  get-include-elt-if ts fn ≫=maybe λ ie →
  trie-lookup (include-elt.import-to-dep ie) ifn ≫=maybe λ ifn' →
  elab-file' ts ρ φ μ ifn' ≫=maybe uncurry''' λ fn ts ρ φ μ →
  lookup-mod-params (toplevel-state.Γ ts) ifn' ≫=maybe λ ps →
  elab-args ts ρ φ μ (as , ps) ≫=maybe (uncurry''' ∘ uncurry) λ as ps ts ρ φ μ →
  elim-pair (scope-file (record ts {Γ = ctxt-set-current-mod (toplevel-state.Γ ts) mod}) fn ifn' oa as) λ ts _ →
  elab-imports ts ρ φ μ is ≫=maybe uncurry''' λ is ts ρ φ μ →
  add-imports ts φ (stringset-strings $ get-all-deps ifn' empty-stringset) (just is) ≫=maybe λ is →
  let i = Import posinfo-gen NotPublic posinfo-gen fn NoOptAs ArgsNil posinfo-gen in
  just (ImportsNext i is , ts , ρ , φ , μ)
  where
  get-all-deps : filepath → stringset → stringset
  get-all-deps fp fs = maybe-else fs (foldr get-all-deps $ stringset-insert fs fp)
    ((maybe-not $ trie-lookup fs fp) ≫=maybe λ _ →
     get-include-elt-if ts fp ≫=maybe
     (just ∘ include-elt.deps))
  add-imports : toplevel-state → renamectxt → 𝕃 string → maybe imports → maybe imports
  add-imports ts φ = flip $ foldl λ fn isₘ → renamectxt-lookup φ fn ≫=maybe λ ifn → isₘ ≫=maybe
    (just ∘ ImportsNext (Import posinfo-gen NotPublic posinfo-gen ifn NoOptAs ArgsNil posinfo-gen))

elab-cmds ts ρ φ μ CmdsStart = just (CmdsStart , ts , ρ , φ , μ)
elab-cmds ts ρ φ μ (CmdsNext (DefTermOrType op (DefTerm _ x NoType t) _) cs) =
  let Γ = toplevel-state.Γ ts in
  elab-synth-term Γ (subst-qualif Γ ρ t) ≫=maybe uncurry λ t T →
  rename qualif-new-var Γ x - x from ρ for λ x' ρ →
  let ts = record ts {Γ = ctxt-term-def' x x' t T op Γ} in
  elab-cmds ts ρ φ μ cs ≫=maybe uncurry λ cs ω →
  just (CmdsNext (DefTermOrType OpacTrans (DefTerm posinfo-gen x' NoType t) posinfo-gen) cs , ω)
elab-cmds ts ρ φ μ (CmdsNext (DefTermOrType op (DefTerm _ x (SomeType T) t) _) cs) =
  let Γ = toplevel-state.Γ ts in
  elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
  elab-check-term Γ (subst-qualif Γ ρ t) T ≫=maybe λ t →
  rename qualif-new-var Γ x - x from ρ for λ x' ρ →
  let ts = record ts {Γ = ctxt-term-def' x x' t T op Γ} in
  elab-cmds ts ρ φ μ cs ≫=maybe uncurry λ cs ω →
  just (CmdsNext (DefTermOrType OpacTrans (DefTerm posinfo-gen x' NoType t) posinfo-gen) cs , ω)
elab-cmds ts ρ φ μ (CmdsNext (DefTermOrType op (DefType _ x _ T) _) cs) =
  let Γ = toplevel-state.Γ ts in
  elab-type Γ (subst-qualif Γ ρ T) ≫=maybe uncurry λ T k →
  rename qualif-new-var Γ x - x from ρ for λ x' ρ →
  let ts = record ts {Γ = ctxt-type-def' x x' T k op Γ} in
  elab-cmds ts ρ φ μ cs ≫=maybe uncurry λ cs ω →
  just (CmdsNext (DefTermOrType OpacTrans (DefType posinfo-gen x' k T) posinfo-gen) cs , ω)
elab-cmds ts ρ φ μ (CmdsNext (DefKind _ x ps k _) cs) =
  let Γ = toplevel-state.Γ ts
      x' = fresh-var (qualif-new-var Γ x) (λ _ → ff) ρ
      ρ = renamectxt-insert ρ x x'
      ts = record ts {Γ = ctxt-kind-def' x x' ps k Γ} in
  elab-cmds ts ρ φ μ cs
elab-cmds ts ρ φ μ (CmdsNext (ImportCmd i) cs) =
  elab-imports ts ρ φ μ (ImportsNext i ImportsStart) ≫=maybe uncurry''' λ is ts ρ φ μ →
  elab-cmds ts ρ φ μ cs ≫=maybe uncurry λ cs ω →
  just (append-cmds (imps-to-cmds is) cs , ω)
elab-cmds ts ρ φ μ (CmdsNext (DefDatatype (Datatype pi pi' x ps k dcs pi'') _) cs) =
  let Γ = toplevel-state.Γ ts
      x' = rename qualif-new-var Γ x - x from ρ for λ x' ρ' → x'
      -- Still need to use x (not x') so constructors work,
      -- but we need to know what it will be renamed to later for μ
      d = defDatatype-to-datatype Γ (Datatype pi pi' x ps k dcs pi'') in
  elim-pair (datatype-encoding.mk-defs selected-encoding Γ d) λ cs' d →
  elab-cmds ts ρ φ (trie-insert μ x' d) (append-cmds cs' cs)

elab-file' ts ρ φ μ fn =
  get-include-elt-if ts fn ≫=maybe λ ie →
  case include-elt.need-to-add-symbols-to-context ie of λ where
    ff → rename fn - base-filename (takeFileName fn) lookup φ for λ fn' φ → just (fn' , ts , ρ , φ , μ)
    tt → include-elt.ast ie ≫=maybe λ where
      (File _ is _ _ mn ps cs _) →
        rename fn - base-filename (takeFileName fn) from φ for λ fn' φ →
        let ie = record ie {need-to-add-symbols-to-context = ff; do-type-check = ff; inv = refl} in
        elab-imports (record (set-include-elt ts fn ie)
          {Γ = ctxt-set-current-file (toplevel-state.Γ ts) fn mn}) ρ φ μ is ≫=maybe uncurry''' λ is ts ρ φ μ →
        elab-params ts ρ φ μ ps ≫=maybe uncurry''' λ ps' ts ρ φ μ →
        let Γ = toplevel-state.Γ ts
            Γ = ctxt-add-current-params (ctxt-set-current-mod Γ (fn , mn , ps' , ctxt-get-qualif Γ)) in
        elab-cmds (record ts {Γ = Γ}) ρ φ μ cs ≫=maybe uncurry' λ cs ts ω →
        let ast = File posinfo-gen ImportsStart posinfo-gen posinfo-gen mn ParamsNil
                    (remove-dup-imports empty-stringset (append-cmds (imps-to-cmds is) cs)) posinfo-gen in
        just (fn' , set-include-elt ts fn (ie-set-span-ast ie (toplevel-state.Γ ts) ast) , ω)
  where
  remove-dup-imports : stringset → cmds → cmds
  remove-dup-imports is CmdsStart = CmdsStart
  remove-dup-imports is (CmdsNext c @ (ImportCmd (Import _ _ _ fp _ _ _)) cs) =
    if stringset-contains is fp
      then remove-dup-imports is cs
      else CmdsNext c (remove-dup-imports (stringset-insert is fp) cs)
  remove-dup-imports is (CmdsNext c cs) = CmdsNext c $ remove-dup-imports is cs

{-# TERMINATING #-}
elab-all : toplevel-state → (from-fp to-fp : string) → IO ⊤
elab-all ts fm to =
  elab-file' prep-ts empty-renamectxt empty-renamectxt empty-trie fm err-code 1 else h
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

  h : (string × toplevel-state × renamectxt × renamectxt × trie encoded-datatype) → IO ⊤
  h' : toplevel-state → renamectxt → stringset → IO ⊤
  h (_ , ts , _ , φ , μ) =
    get-file-imports ts fm (trie-single fm triv) err-code 3 else h' ts φ
  h' ts φ is = foldr
    (λ fn x → x >>= λ e →
      maybe-else
        (return ff)
        (uncurry λ fn ie →
          writeRopeToFile (combineFileNames to fn ^ ".ced")
            (maybe-else [[ "Error lookup up elaborated data" ]] id (ie-get-span-ast ie)) >>
          return e)
      (renamectxt-lookup φ fn ≫=maybe λ fn' →
       get-include-elt-if ts fn ≫=maybe λ ie →
       include-elt.ast ie ≫=maybe λ ast → just (fn' , ie)))
    (createDirectoryIfMissing tt to >> return tt)
    (stringset-strings is) >>= λ e →
    putStrLn (if e then "0" else "2")

elab-file : toplevel-state → (filename : string) → maybe rope
elab-file ts fn =
  elab-file' ts empty-renamectxt empty-renamectxt empty-trie fn ≫=maybe uncurry'' λ fn' ts ρ φ →
  get-include-elt-if ts fn ≫=maybe ie-get-span-ast





