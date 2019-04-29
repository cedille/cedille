import cedille-options
open import general-util
module classify (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib

open import cedille-types
open import constants
open import conversion
open import ctxt
open import datatype-functions
open import is-free
open import lift
open import rename
open import rewriting
open import meta-vars options {mF}
open import spans options {mF}
open import subst
open import syntax-util
open import to-string options
open import untyped-spans options {mF}

check-ret : ∀{A : Set} → maybe A → Set
check-ret{A} nothing = maybe A
check-ret (just _) = ⊤

infixl 2 _≫=spanr_ 
_≫=spanr_ : ∀{A : Set}{m : maybe A} → spanM (maybe A) → (A → spanM (check-ret m)) → spanM (check-ret m)
_≫=spanr_{m = nothing} = _≫=spanm_
_≫=spanr_{m = just _} = _≫=spanj_

-- return the appropriate value meaning that typing failed (in either checking or synthesizing mode)
check-fail : ∀{A : Set} → (m : maybe A) → spanM (check-ret m)
check-fail nothing = spanMr nothing
check-fail (just _) = spanMok

unimplemented-check : spanM ⊤
unimplemented-check = spanMok

unimplemented-synth : ∀{A : Set} → spanM (maybe A)
unimplemented-synth = spanMr nothing

unimplemented-if : ∀{A : Set} → (m : maybe A) → spanM (check-ret m)
unimplemented-if nothing = unimplemented-synth
unimplemented-if (just _) = unimplemented-check

-- return the second maybe value, if we are in synthesizing mode
return-when : ∀{A : Set} → (m : maybe A) → maybe A → spanM (check-ret m)
return-when nothing u = spanMr u
return-when (just _) u = spanMr triv

-- if m is not "nothing", return "just star"
return-star-when : (m : maybe kind) → spanM (check-ret m)
return-star-when m = return-when m (just star)

if-check-against-star-data : ctxt → string → maybe kind → 𝕃 tagged-val × err-m
if-check-against-star-data Γ desc nothing = [ kind-data Γ star ] , nothing
if-check-against-star-data Γ desc (just (Star _)) = [ kind-data Γ star ] , nothing
if-check-against-star-data Γ desc (just k) = [ expected-kind Γ k ] , just (desc ^ " is being checked against a kind other than ★")

hnf-from : ctxt → (e : 𝔹) → maybeMinus → term → term
hnf-from Γ e EpsHnf t = hnf Γ (unfolding-set-erased unfold-head e) t tt
hnf-from Γ e EpsHanf t = hanf Γ e t

maybe-hnf : {ed : exprd} → ctxt → maybe ⟦ ed ⟧ → maybe ⟦ ed ⟧
maybe-hnf Γ = maybe-map λ t → hnf Γ (unfolding-elab unfold-head) t tt

check-term-update-eq : ctxt → leftRight → maybeMinus → posinfo → term → term → posinfo → type
check-term-update-eq Γ Left m pi t1 t2 pi' = TpEq pi (hnf-from Γ tt m t1) t2 pi'
check-term-update-eq Γ Right m pi t1 t2 pi' = TpEq pi t1 (hnf-from Γ tt m t2)  pi'
check-term-update-eq Γ Both m pi t1 t2 pi' = TpEq pi (hnf-from Γ tt m t1) (hnf-from Γ tt m t2) pi'

add-tk-with-err-m : maybeErased → 𝕃 tagged-val → err-m → posinfo → var → tk → spanM restore-def
add-tk-with-err-m e tags em pi x atk = 
   helper atk ≫=span λ mi → 
    (if ~ (x =string ignored-var) then
       (get-ctxt λ Γ → 
          spanM-add (var-span-with-tags e Γ pi x checking atk tags em))
    else spanMok) ≫span
   spanMr mi
  where helper : tk → spanM restore-def
        helper (Tkk k) = spanM-push-type-decl pi x k 
        helper (Tkt t) = spanM-push-term-decl pi x t

add-tk' : maybeErased → posinfo → var → tk → spanM restore-def
add-tk' e = add-tk-with-err-m e [] nothing

add-tk : posinfo → var → tk → spanM restore-def
add-tk = add-tk' ff

check-type-return : ctxt → kind → spanM (maybe kind)
check-type-return Γ k = spanMr (just (hnf Γ (unfolding-elab unfold-head) k tt))

check-termi-return-hnf : ctxt → (subject : term) → type → spanM (maybe type)
check-termi-return-hnf Γ subject tp = spanMr (just (hnf Γ (unfolding-elab unfold-head) tp tt))

lambda-bound-var-conv-error : ctxt → var → tk → tk → 𝕃 tagged-val → 𝕃 tagged-val × string
lambda-bound-var-conv-error Γ x atk atk' tvs =
  (("the variable" , [[ x ]] , []) :: (to-string-tag-tk "its declared classifier" Γ atk') :: [ to-string-tag-tk "the expected classifier" Γ atk ]) ++ tvs ,
  "The classifier given for a λ-bound variable is not the one we expected"

lambda-bound-class-if : optClass → tk → tk
lambda-bound-class-if NoClass atk = atk
lambda-bound-class-if (SomeClass atk') atk = atk'

{- for check-term and check-type, if the optional classifier is given, we will check against it.
   Otherwise, we will try to synthesize a type.  
   check-type should return kinds in hnf using check-type-return.
   Use add-tk above to add declarations to the ctxt, since these should be normalized
   and with self-types instantiated.
   
   The term/type/kind being checked is never qualified, but the type/kind it is being
   checked against should always be qualified. So if a term/type is ever being checked
   against something that was in a term/type the user wrote (phi, for example, needs to
   check its first term against an equation between its second and third terms), the type/
   kind being checked against should be qualified first. Additionally, when returning
   a synthesized type, lambdas should substitute the position-qualified variable for the
   original variable in the returned type, so that if the bound variable ever gets
   substituted by some other code it will work correctly.
 -}
record spine-data : Set where
  constructor mk-spine-data
  field
    spine-mvars : meta-vars
    spine-type : decortype
    spine-locale : ℕ

{-# TERMINATING #-}
check-term : term → (m : maybe type) → spanM (check-ret m)
check-termi : term → (m : maybe type) → spanM (check-ret m)
check-term-spine : term → (m : prototype) → 𝔹 → spanM (maybe spine-data)
check-type : type → (m : maybe kind) → spanM (check-ret m)
check-typei : type → (m : maybe kind) → spanM (check-ret m)
check-kind : kind → spanM ⊤
check-args-against-params : (kind-or-import : maybe tagged-val {- location -}) → (posinfo × var) → params → args → spanM ⊤
check-erased-margs : term → maybe type → spanM ⊤
check-tk : tk → spanM ⊤
check-def : defTermOrType → spanM (posinfo × var × restore-def × Σ tk λ atk → if tk-is-type atk then term else type)
check-mu : posinfo → posinfo → (μ-or-μ' : maybe var) → term → (evidence : optTerm) → (motive : optType) → posinfo → cases → posinfo → (mtp : maybe type) → spanM (check-ret mtp)
check-mu-evidence : optTerm → var → 𝕃 tty → spanM ((string × 𝕃 tagged-val) ⊎ maybe ((term → term) × ctxt-datatype-info))
check-case : case → (ctrs : trie (maybe type)) → (ctr-ps : args) → (drop-as : ℕ) → type → spanM (trie (maybe type) × 𝕃 (posinfo × var × tk × maybeErased × posinfo × posinfo))
check-cases : cases → (ctrs : trie type) → (ctr-ps : args) → (drop-as : ℕ) → type → spanM (err-m × 𝕃 (posinfo × var × tk × maybeErased × posinfo × posinfo))

-- check-term
-- ==================================================

module check-term-errors {A : Set} where
  inapplicable-tp : (t : term) (tp : type) (htp : type) (mtp : maybe type) → spanM $ check-ret mtp
  inapplicable-tp t tp htp m =
    get-ctxt λ Γ →
    spanM-add (AppTp-span t tp (maybe-to-checking m)
      ([ head-type Γ htp ])
      (just "The type of the head does not allow it to be applied to a type argument"))
    ≫span (spanMr $ ret m)
    where
    ret : (m : maybe type) → check-ret m
    ret (just x₁) = triv
    ret nothing = nothing

check-term t nothing = check-termi t nothing ≫=span λ T → get-ctxt λ Γ → spanMr (maybe-map (λ T → hnf Γ (unfolding-elab unfold-head) T ff) T)
check-term t (just T) = get-ctxt λ Γ → check-termi t (just (hnf Γ (unfolding-elab unfold-head) T ff))
--check-term = check-termi -- Used to call hnf on expected/synthesized type

check-type subject nothing = check-typei subject nothing
check-type subject (just k)
  = get-ctxt (λ Γ → check-typei subject (just (hnf Γ (unfolding-elab unfold-head) k tt)))

check-termi (Parens pi t pi') tp =
  spanM-add (punctuation-span "Parens" pi pi') ≫span
  check-termi t tp
check-termi (Var pi x) mtp =
  get-ctxt (cont mtp)
  where        
  cont : (mtp : maybe type) → ctxt → spanM (check-ret mtp)
  cont mtp Γ with ctxt-lookup-term-var Γ x
  cont mtp Γ | nothing =
    spanM-add (Var-span Γ pi x (maybe-to-checking mtp)
        (expected-type-if Γ mtp ++ [ missing-type ])
        (just "Missing a type for a term variable.")) ≫span
    return-when mtp mtp
  cont nothing Γ | just tp =
    spanM-add (Var-span Γ pi x synthesizing [ type-data Γ tp ] nothing) ≫span
    spanMr (just tp)
  cont (just tp) Γ | just tp' =
    spanM-add (uncurry (Var-span Γ pi x checking)
      (check-for-type-mismatch Γ "synthesized" tp tp'))

check-termi t'@(AppTp t tp') mtp =
  get-ctxt λ Γ →
  check-termi t nothing
    on-fail spanM-add (AppTp-span t tp' (maybe-to-checking mtp)
              (expected-type-if Γ mtp) nothing)
            ≫span return-when mtp mtp
  ≫=spanm' λ tp → spanMr (either-else' (to-is-tpabs tp)
      (λ _ → to-is-tpabs (hnf Γ (unfolding-elab unfold-head) tp tt)) inj₂)
    on-fail (λ _ → check-term-errors.inapplicable-tp {A = check-ret mtp} t tp' tp mtp)
  ≫=spans' λ ret → let mk-tpabs e? x k body = ret in
  check-type tp' (just k)
  ≫span
    let rtp = subst Γ (qualif-type Γ tp') x body in
    spanM-add (uncurry (λ tvs →
      AppTp-span t tp' (maybe-to-checking mtp) (type-data Γ rtp :: tvs))
      (check-for-type-mismatch-if Γ "synthesizing" mtp rtp))
  ≫span return-when mtp (just rtp)


check-termi t''@(App t m t') tp =
  get-ctxt λ Γ → check-term-spine t'' (proto-maybe tp) tt
    on-fail check-fail tp
  ≫=spanm' λ where
    (mk-spine-data Xs tp' _) → return-when tp (just (meta-vars-subst-type' ff Γ Xs (decortype-to-type tp')))

check-termi (Let pi fe d t) mtp =
  -- spanM-add (punctuation-span "Let" pi (posinfo-plus pi 3)) ≫span
  check-def d ≫=span finish
  where maybe-subst : defTermOrType → (mtp : maybe type) → check-ret mtp → spanM (check-ret mtp)
        maybe-subst _ (just T) triv = spanMok
        maybe-subst _ nothing nothing = spanMr nothing
        maybe-subst (DefTerm pi x NoType t) nothing (just T) = get-ctxt λ Γ →
          spanMr (just (subst Γ (qualif-term Γ (Chi posinfo-gen NoType t)) (pi % x) T))
        maybe-subst (DefTerm pi x (SomeType T') t) nothing (just T) = get-ctxt λ Γ →
          spanMr (just (subst Γ (qualif-term Γ (Chi posinfo-gen (SomeType T') t)) (pi % x) T))
        maybe-subst (DefType pi x k T') nothing (just T) = get-ctxt λ Γ →
          spanMr (just (subst Γ (qualif-type Γ T') (pi % x) T))
        -- maybe-subst covers the case where the synthesized type of t has the let-bound
        -- variable in it by substituting the let definition for the let-bound variable
        -- in the synthesized type. We also need to use Chi to maintain the checking mode
        -- of the term so that the type still kind-checks, as a synthesizing term let could
        -- be substituted into a checking position, or vice-versa with a checking term let.

        occurs : err-m
        occurs =
          if defTermOrType-is-term d && fe && is-free-in skip-erased (defTermOrType-get-var d) t
          then just "The bound variable occurs free in the erasure of the body" else nothing

        finish : (posinfo × var × restore-def × Σ tk λ atk → if tk-is-type atk then term else type) → spanM (check-ret mtp)
        finish (pi' , x , m , atk , val) = 
         get-ctxt λ Γ → 
         spanM-add (Let-span Γ (maybe-to-checking mtp) pi pi' fe x atk val t [] occurs) ≫span
         check-term t mtp ≫=span λ r →
         spanM-restore-info x m ≫span
         maybe-subst d mtp r

check-termi (Open pi o pi' x t) mtp = get-ctxt λ Γ →
   spanMr (ctxt-get-qi Γ x) on-fail genNoDefErr
  ≫=spanm' λ qi → let x' = fst qi in
   spanM-clarify-def o x'   on-fail genCategoryErr
  ≫=spanm' λ si → (spanM-add $ open-span Γ nothing)
  ≫span get-ctxt λ Γ' → spanMr (ctxt-lookup-var Γ' x) on-fail genNoDefErr
  ≫=spanm' λ tk → (case tk of λ where
    (Tkt tp) → spanM-add $ Var-span Γ' pi' x mode [ type-data Γ tp ] nothing
    (Tkk k)  → spanM-add $ TpVar-span Γ' pi' x mode [ kind-data Γ k ] nothing
  ) ≫span check-term t mtp
  ≫=span λ tp → spanM-restore-clarified-def x' si ≫span spanMr tp

  where
  mode = maybe-to-checking mtp

  open-span : ctxt → err-m → span
  open-span Γ = Open-span Γ o pi x t mode []

  genNoDefErr : spanM (check-ret mtp)
  genNoDefErr = get-ctxt λ Γ →
    spanM-add (open-span Γ (just $ x ^ " is not in scope"))
    ≫span check-fail mtp

  genCategoryErr : spanM (check-ret mtp)
  genCategoryErr = get-ctxt λ Γ →
    spanM-add (open-span Γ (just $ x ^ " is not a type or term definition"))
    ≫span check-fail mtp

check-termi (Lam pi l pi' x (SomeClass atk) t) nothing =
  spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
    add-tk pi' x atk ≫=span λ mi → 
    check-term t nothing ≫=span λ mtp → 
    get-ctxt λ Γ →
    spanM-restore-info x mi ≫span -- now restore the context
    cont mtp Γ

  where cont : maybe type → (old-ctxt : ctxt) → spanM (maybe type)
        cont nothing Γ' =
          get-ctxt λ Γ → 
          spanM-add (Lam-span Γ' synthesizing pi pi' l x atk t [] nothing) ≫span 
          spanMr nothing
        cont (just tp) Γ' =
          get-ctxt λ Γ → 
          let atk' = qualif-tk Γ atk in
          -- This should indeed "unqualify" occurrences of x in tp for rettp
          let rettp = abs-tk l x atk' (rename-var Γ (pi' % x) x tp) in
          let tvs = [ type-data Γ rettp ] in
          let p = if l && is-free-in skip-erased x t then just "The bound variable occurs free in the erasure of the body (not allowed)." , [ erasure Γ t ] else nothing , [] in
          spanM-add (Lam-span Γ' synthesizing pi pi' l x atk' t (snd p ++ tvs) (fst p)) ≫span
          check-termi-return-hnf Γ (Lam pi l pi' x (SomeClass atk) t) rettp

check-termi (Lam pi l pi' x NoClass t) nothing =
  get-ctxt λ Γ → 
  spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
  spanM-add (Lam-span (ctxt-var-decl-loc pi' x Γ) synthesizing pi pi' l x (Tkt $ TpHole pi') t []
              (just ("We are not checking this abstraction against a type, so a classifier must be"
                          ^ " given for the bound variable " ^ x))) ≫span
  spanMr nothing

check-termi (Lam pi l pi' x oc t) (just tp) =
  get-ctxt λ Γ → cont (to-abs tp maybe-or to-abs (hnf Γ (unfolding-elab unfold-head) tp tt)) where
    cont : maybe abs → spanM ⊤
    cont (just (mk-abs b x' atk _ tp')) =
      check-oc oc ≫span
      spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
      get-ctxt λ Γ →
      (uncurry (add-tk-with-err-m l) (check-erasures Γ l b) pi' x (lambda-bound-class-if oc atk)) ≫=span λ mi → 
      get-ctxt λ Γ' →
      spanM-add (this-span Γ atk oc [ type-data Γ tp ] nothing) ≫span
      check-term t (just (rename-var Γ x' (qualif-var Γ' x) tp')) ≫span
      spanM-restore-info x mi where
        this-span : ctxt → tk → optClass → 𝕃 tagged-val → err-m → span
        this-span Γ atk NoClass tvs = Lam-span Γ checking pi pi' l x atk t tvs
        this-span Γ atk (SomeClass atk') tvs err = 
          if conv-tk Γ (qualif-tk Γ atk') atk then
            Lam-span Γ checking pi pi' l x atk' t tvs err
          else
            let p = lambda-bound-var-conv-error Γ x atk (qualif-tk Γ atk') tvs in
            Lam-span Γ checking pi pi' l x atk' t (fst p) (just (snd p))
        check-oc : optClass → spanM ⊤
        check-oc NoClass = spanMok
        check-oc (SomeClass atk) = check-tk atk
        check-erasures : ctxt → maybeErased → maybeErased → 𝕃 tagged-val × err-m
        check-erasures Γ Erased All = 
          if is-free-in skip-erased x t
            then [ erasure Γ t ] , just "The Λ-bound variable occurs free in the erasure of the body."
            else [] , nothing
        check-erasures Γ NotErased Pi = [] , nothing
        check-erasures Γ Erased Pi =  [] , just ("The expected type is a Π-abstraction (indicating explicit input), but"
                                              ^ " the term is a Λ-abstraction (implicit input).")
        check-erasures Γ NotErased All =  [] , just ("The expected type is a ∀-abstraction (indicating implicit input), but"
                                              ^ " the term is a λ-abstraction (explicit input).")
    cont nothing =
      get-ctxt λ Γ →
      spanM-add (punctuation-span "Lambda"  pi (posinfo-plus pi 1)) ≫span
      spanM-add (Lam-span Γ checking pi pi' l x (Tkt $ TpHole pi') t [ expected-type Γ tp ] (just "The expected type is not of the form that can classify a λ-abstraction"))


check-termi (Beta pi ot ot') (just tp) =
  untyped-optTerm-spans ot ≫span
  untyped-optTerm-spans ot' ≫span
  get-ctxt λ Γ →
  spanM-add (uncurry (Beta-span pi (optTerm-end-pos-beta pi ot ot') checking)
    (case hnf Γ unfold-head tp tt of λ where
      (TpEq pi' t1 t2 pi'') → 
        if conv-term Γ t1 t2
          then [ type-data Γ (TpEq pi' t1 t2 pi'') ] , (optTerm-conv Γ t1 ot)
          else [ expected-type Γ (TpEq pi' t1 t2 pi'') ] , (just "The two terms in the equation are not β-equal")
      tp → [ expected-type Γ tp ] , just "The expected type is not an equation."))
  where
    optTerm-conv : ctxt → term → optTerm → err-m
    optTerm-conv Γ t1 NoTerm = nothing
    optTerm-conv Γ t1 (SomeTerm t _) = if conv-term Γ (qualif-term Γ t) t1 then nothing else just "The expected type does not match the synthesized type"

check-termi (Beta pi (SomeTerm t pi') ot) nothing =
  get-ctxt λ Γ →
  untyped-term-spans t ≫span
  untyped-optTerm-spans ot ≫span
  let tp = qualif-type Γ (TpEq posinfo-gen t t posinfo-gen) in
  spanM-add (Beta-span pi (optTerm-end-pos-beta pi (SomeTerm t pi') ot) synthesizing [ type-data Γ tp ] nothing) ≫span
  spanMr (just tp)

check-termi (Beta pi NoTerm ot') nothing = 
  untyped-optTerm-spans ot' ≫span
  spanM-add (Beta-span pi (optTerm-end-pos-beta pi NoTerm ot') synthesizing [] (just "An expected type is required in order to type a use of plain β.")) ≫span
  spanMr nothing

check-termi (Epsilon pi lr m t) (just tp) = -- (TpEq pi' t1 t2 pi'')) = 
  get-ctxt λ Γ → 
  case hnf Γ unfold-head tp tt of λ where
    (TpEq pi' t1 t2 pi'') →
      spanM-add (Epsilon-span pi lr m t checking [ type-data Γ (TpEq pi' t1 t2 pi'') ] nothing) ≫span
      check-term t (just (check-term-update-eq Γ lr m pi' t1 t2 pi''))
    tp → spanM-add (Epsilon-span pi lr m t checking [ expected-type Γ tp ] (just "The expected type is not an equation, when checking an ε-term."))

check-termi (Epsilon pi lr m t) nothing = 
  check-term t nothing ≫=span λ mtp → get-ctxt λ Γ → cont (maybe-hnf Γ mtp)
  where cont : maybe type → spanM (maybe type)
        cont nothing = 
          spanM-add (Epsilon-span pi lr m t synthesizing []
            (just "There is no expected type, and we could not synthesize a type from the body of the ε-term.")) ≫span
          spanMr nothing
        cont (just (TpEq pi' t1 t2 pi'')) =
          get-ctxt λ Γ → 
          let r = check-term-update-eq Γ lr m pi' t1 t2 pi'' in
          spanM-add (Epsilon-span pi lr m t synthesizing [ type-data Γ r ] nothing) ≫span
          spanMr (just r)
        cont (just tp) = 
          get-ctxt λ Γ → 
          spanM-add (Epsilon-span pi lr m t synthesizing [ to-string-tag "the synthesized type" Γ tp ]
            (just "There is no expected type, and the type we synthesized for the body of the ε-term is not an equation.")) ≫span
          spanMr nothing

check-termi (Sigma pi t) nothing = get-ctxt λ Γ →
    check-term t nothing
      on-fail errSynthBody
  ≫=spanm' λ tp → spanMr (is-eq-tp? (hnf Γ (unfolding-elab unfold-head) tp tt))
      on-fail errSynthNonEq Γ tp
  ≫=spanm' λ ret →
    let mk-eq-tp! t₁ t₂ pi₁ pi₂ = ret in
    let tp' = TpEq posinfo-gen t₂ t₁ posinfo-gen in
    spanM-add (Sigma-span pi t synthesizing [ type-data Γ tp' ] nothing)
  ≫span (spanMr ∘ just $ tp')

  where
  errSynthBody : spanM (maybe type)
  errSynthBody =
      spanM-add (Sigma-span pi t synthesizing []
        (just "We could not synthesize a type from the body of the ς-term"))
    ≫span check-fail nothing

  errSynthNonEq : ctxt → type → spanM (maybe type)
  errSynthNonEq Γ tp =
    spanM-add (Sigma-span pi t synthesizing ([ to-string-tag "synthesized type" Γ tp ])
      (just ("The type we synthesized for the body of the ς-term is not an equation")))
    ≫span check-fail nothing

check-termi (Sigma pi t) (just tp) = get-ctxt λ Γ →
  let eq? : maybe is-eq-tp!
      eq? = is-eq-tp? (hnf Γ (unfolding-elab unfold-head) tp tt)
  in spanMr eq? on-fail errChkNotEq Γ
  ≫=spanm' λ ret → let mk-eq-tp! lhs rhs lpi rpi = ret in
    check-termi t (just $ TpEq posinfo-gen rhs lhs posinfo-gen)
  ≫span spanM-add (Sigma-span pi t checking [ expected-type Γ (TpEq lpi lhs rhs rpi) ] nothing)

  where
  errChkNotEq : ctxt → spanM ⊤
  errChkNotEq Γ =
      spanM-add (Sigma-span pi t checking [ expected-type Γ tp ]
                  (just "The expected type is not (convertible to) an equation"))

check-termi (Phi pi t₁≃t₂ t₁ t₂ pi') (just tp) =
  get-ctxt λ Γ →
  check-term t₁≃t₂ (just (qualif-type Γ (TpEq posinfo-gen t₁ t₂ posinfo-gen))) ≫span
  check-term t₁ (just tp) ≫span
  untyped-term-spans t₂ ≫span
  spanM-add (Phi-span pi pi' checking [ type-data Γ tp ] nothing)

check-termi (Phi pi t₁≃t₂ t₁ t₂ pi') nothing =
  get-ctxt λ Γ →
  check-term t₁≃t₂ (just (qualif-type Γ (TpEq posinfo-gen t₁ t₂ posinfo-gen))) ≫span
  check-term t₁ nothing ≫=span λ mtp →
  untyped-term-spans t₂ ≫span
  spanM-add (Phi-span pi pi' synthesizing (type-data-tvs Γ mtp) nothing) ≫span
  spanMr mtp
    where
      type-data-tvs : ctxt → maybe type → 𝕃 tagged-val
      type-data-tvs Γ (just tp) = [ type-data Γ tp ]
      type-data-tvs Γ nothing = []


check-termi (Rho pi op on t (Guide pi' x tp) t') nothing =
  get-ctxt λ Γ →
  spanM-add (Var-span (ctxt-var-decl-loc pi' x Γ) pi' x synthesizing [] nothing) ≫span
  check-term t' nothing ≫=span λ mtp →
  untyped-optGuide-spans (Guide pi' x tp) ≫=span λ tvs →
  check-term t nothing ≫=span λ mtp' → case maybe-hnf Γ mtp' of λ where
    (just (TpEq _ t1 t2 _)) → maybe-else
      (spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) tvs nothing) ≫span spanMr nothing)
      (λ tp' →
        let Γ' = ctxt-var-decl-loc pi' x Γ
            tp = qualif-type Γ' tp
            tp'' = subst Γ t2 x tp
            qt = qualif-term Γ t
            tp''' = post-rewrite Γ' x qt t1 (rewrite-at Γ' x (just qt) tt tp' tp) in
        if conv-type Γ tp'' tp'
          then (spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) (type-data Γ tp''' :: tvs) nothing) ≫span spanMr (just tp'''))
          else (spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) (type-data Γ tp' :: expected-type-subterm Γ tp'' :: tvs)
            (just "The expected type of the subterm does not match the synthesized type")) ≫span spanMr nothing)) mtp
    (just _) → spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) tvs
                 (just "We could not synthesize an equation from the first subterm in a ρ-term.")) ≫span spanMr nothing
    nothing → spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) tvs nothing) ≫span check-term t' nothing

check-termi (Rho pi op on t (Guide pi' x tp) t') (just tp') =
  get-ctxt λ Γ →
  untyped-optGuide-spans (Guide pi' x tp) ≫=span λ tvs →
  check-term t nothing ≫=span λ mtp → case maybe-hnf Γ mtp of λ where
    (just (TpEq _ t1 t2 _)) →
      let Γ' = ctxt-var-decl-loc pi' x Γ
          qt = qualif-term Γ t
          tp = qualif-type Γ' tp
          tp'' = subst Γ' t1 x tp
          tp''' = post-rewrite Γ' x qt t2 (rewrite-at Γ' x (just qt) tt tp' tp)
          err = if conv-type Γ tp'' tp' then nothing else just "The expected type does not match the specified type" in
      spanM-add (Rho-span pi t t' checking op (inj₂ x) (type-data Γ tp'' :: expected-type Γ tp' :: tvs) err) ≫span
      spanM-add (Var-span (ctxt-var-decl-loc pi' x Γ) pi' x checking [] nothing) ≫span
      check-term t' (just tp''')
    (just _) → spanM-add (Rho-span pi t t' checking op (inj₂ x) tvs
                 (just "We could not synthesize an equation from the first subterm in a ρ-term."))
    nothing → spanM-add (Rho-span pi t t' checking op (inj₂ x) tvs nothing) ≫span check-term t' (just tp)

check-termi (Rho pi op on t NoGuide t') (just tp) =
  get-ctxt λ Γ → check-term t nothing ≫=span λ mtp →
  cont (maybe-hnf Γ mtp) (hnf Γ (unfolding-elab unfold-head-no-lift) tp tt)
  where cont : maybe type → type → spanM ⊤
        cont nothing tp = get-ctxt λ Γ → spanM-add (Rho-span pi t t' checking op (inj₁ 0) [ expected-type Γ tp ] nothing) ≫span check-term t' (just tp)
        cont (just (TpEq pi' t1 t2 pi'')) tp = 
           get-ctxt λ Γ →
             let ns-err = optNums-to-stringset on
                 x = fresh-var Γ "x"
                 Γ' = ctxt-var-decl x Γ
                 qt = qualif-term Γ t
                 s = rewrite-type tp Γ' op (fst ns-err) (just qt) t1 x 0
                 T = post-rewrite Γ' x qt t2 (fst s) in -- subst-type Γ' t2 x (fst s) in
             check-term t' (just T) ≫span
             spanM-add (Rho-span pi t t' checking op (inj₁ (fst (snd s))) ((to-string-tag "the equation" Γ (TpEq pi' t1 t2 pi'')) :: [ type-data Γ tp ]) (snd ns-err (snd (snd s))))
        cont (just tp') tp =
          get-ctxt λ Γ → spanM-add (Rho-span pi t t' checking op (inj₁ 0)
                                     ((to-string-tag "the synthesized type for the first subterm" Γ tp')
                                       :: [ expected-type Γ tp ])
                                     (just "We could not synthesize an equation from the first subterm in a ρ-term."))

check-termi (Rho pi op on t NoGuide t') nothing = 
  check-term t nothing ≫=span λ mtp → 
  check-term t' nothing ≫=span λ mtp' → get-ctxt λ Γ → cont (maybe-hnf Γ mtp)
    (maybe-map (λ mtp' → hnf Γ (unfolding-elab unfold-head-no-lift) mtp' tt) mtp')
  where cont : maybe type → maybe type → spanM (maybe type)
        cont (just (TpEq pi' t1 t2 pi'')) (just tp) = 
          get-ctxt λ Γ → 
            let ns-err = optNums-to-stringset on
                x = fresh-var Γ "x"
                qt = qualif-term Γ t
                Γ' = ctxt-var-decl x Γ
                s = rewrite-type tp Γ' op (fst ns-err) (just qt) t2 x 0
                tp' = post-rewrite Γ' x qt t1 (fst s) in
              spanM-add (Rho-span pi t t' synthesizing op (inj₁ (fst (snd s))) [ type-data Γ tp' ] (snd ns-err (snd (snd s)))) ≫span
              check-termi-return-hnf Γ (Rho pi op on t NoGuide t') tp'
        cont (just tp') (just _) =
           get-ctxt λ Γ → spanM-add (Rho-span pi t t' synthesizing op (inj₁ 0) [ to-string-tag "the synthesized type for the first subterm" Γ tp' ]
                                         (just "We could not synthesize an equation from the first subterm in a ρ-term.")) ≫span spanMr nothing
        cont _ _ = spanM-add (Rho-span pi t t' synthesizing op (inj₁ 0) [] nothing) ≫span spanMr nothing

check-termi (Chi pi (SomeType tp) t) mtp =
  check-type tp (just star) ≫span
  get-ctxt λ Γ →
  let tp' = qualif-type Γ tp in
  check-termi t (just tp') ≫span cont tp' mtp
  where cont : type → (m : maybe type) → spanM (check-ret m)
        cont tp' nothing = get-ctxt λ Γ → spanM-add (Chi-span Γ pi (SomeType tp) t synthesizing [] nothing) ≫span spanMr (just tp')
        cont tp' (just tp'') =
          get-ctxt λ Γ → 
          spanM-add (uncurry (Chi-span Γ pi (SomeType tp') t checking) (check-for-type-mismatch Γ "asserted" tp'' tp'))
check-termi (Chi pi NoType t) (just tp) = 
  check-term t nothing ≫=span cont 
  where cont : (m : maybe type) → spanM ⊤
        cont nothing = get-ctxt (λ Γ → spanM-add (Chi-span Γ pi NoType t checking [] nothing) ≫span spanMok)
        cont (just tp') =
          get-ctxt λ Γ → 
          spanM-add (uncurry (Chi-span Γ pi NoType t checking) (check-for-type-mismatch Γ "synthesized" tp tp'))
check-termi (Chi pi NoType t) nothing =
 get-ctxt λ Γ → spanM-add (Chi-span Γ pi NoType t synthesizing [] nothing) ≫span check-term t nothing

check-termi (Delta pi mT t) mtp =
  check-term t nothing ≫=span λ T →
  get-ctxt λ Γ →
  spanM-add (Delta-span Γ pi mT t (maybe-to-checking mtp) [] (maybe-hnf Γ T ≫=maybe check-contra Γ)) ≫span
  (case mT of λ where
    NoType → spanMr compileFailType
    (SomeType T) → check-type T (just (Star posinfo-gen)) ≫span spanMr T) ≫=span λ T → 
  return-when mtp (just (qualif-type Γ T))
  where check-contra : ctxt → type → err-m
        check-contra Γ (TpEq _ t1 t2 _) =
          if inconv Γ t1 t2 -- check-beta-inequiv (hnf Γ unfold-head t1 tt) (hnf Γ unfold-head t2 tt)
            then nothing
            else just "We could not find a contradiction in the synthesized type of the subterm."
        check-contra _ _ = just "We could not synthesize an equation from the subterm."

check-termi (Theta pi u t ls) nothing =
  get-ctxt λ Γ →
  spanM-add (Theta-span Γ pi u t ls synthesizing []
               (just "Theta-terms can only be used in checking positions (and this is a synthesizing one)."))
  ≫span spanMr nothing

check-termi (Theta pi AbstractEq t ls) (just tp) =
  -- discard spans from checking t, because we will check it again below
  check-term t nothing ≫=spand λ mtp → get-ctxt λ Γ → cont (maybe-hnf Γ mtp) (hnf Γ (unfolding-elab unfold-head) tp tt)
  where cont : maybe type → type → spanM ⊤
        cont nothing tp = check-term t nothing ≫=span λ m → 
                       get-ctxt λ Γ →
                          spanM-add (Theta-span Γ pi AbstractEq t ls checking [ expected-type Γ tp ] (just "We could not compute a motive from the given term"))
                                      -- (expected-type Γ tp :: [ motive-label , [[ "We could not compute a motive from the given term" ]] , [] ]))))
        cont (just htp) tp =
           get-ctxt λ Γ → 
             let x = fresh-var Γ "x"
                 motive = mtplam x (Tkt htp) (TpArrow (TpEq posinfo-gen t (mvar x) posinfo-gen) Erased tp) in
               spanM-add (Theta-span Γ pi AbstractEq t ls checking (expected-type Γ tp :: [ the-motive Γ motive ]) nothing) ≫span 
               check-term (lterms-to-term AbstractEq (AppTp t (NoSpans motive (posinfo-plus (term-end-pos t) 1))) ls)
                 (just tp)

check-termi (Theta pi Abstract t ls) (just tp) =
  -- discard spans from checking the head, because we will check it again below
  check-term t nothing ≫=spand λ mtp → get-ctxt λ Γ → cont t (maybe-hnf Γ mtp) (hnf Γ unfold-head tp tt)
  where cont : term → maybe type → type → spanM ⊤
        cont _ nothing tp = check-term t nothing ≫=span λ m → 
                         get-ctxt λ Γ →
                           spanM-add (Theta-span Γ pi Abstract t ls checking [ expected-type Γ tp ] (just "We could not compute a motive from the given term"))
                                      -- (expected-type Γ tp :: [ motive-label , [[ "We could not compute a motive from the given term" ]] , [] ]))))
        cont t (just htp) tp = 
          get-ctxt λ Γ →
          let x = compute-var (hnf Γ unfold-head (qualif-term Γ t) tt)
              x' = maybe-else (unqual-local x) id (var-suffix x) in
          let motive = mtplam x' (Tkt htp) (rename-var Γ x x' tp) in
            spanM-add (Theta-span Γ pi Abstract t ls checking (expected-type Γ tp :: [ the-motive Γ motive ]) nothing) ≫span 
            check-term (lterms-to-term Abstract (AppTp t (NoSpans motive (term-end-pos t))) ls) 
               (just tp)
          where compute-var : term → var
                compute-var (Var pi' x) = x
                compute-var t = ignored-var

check-termi (Theta pi (AbstractVars vs) t ls) (just tp) =
  get-ctxt λ Γ → let tp = hnf Γ (unfolding-elab unfold-head) tp tt in cont (wrap-vars Γ vs tp {-(substs-type empty-ctxt (rep-vars Γ vs empty-trie) tp)-}) tp
  where wrap-var : ctxt → var → type → maybe type
        wrap-var Γ v tp = ctxt-lookup-tk-var Γ v ≫=maybe λ atk → just (mtplam v atk (rename-var Γ (qualif-var Γ v) v tp))
        wrap-vars : ctxt → vars → type → maybe type
        wrap-vars Γ (VarsStart v) tp = wrap-var Γ v tp
        wrap-vars Γ (VarsNext v vs) tp = wrap-vars Γ vs tp ≫=maybe wrap-var Γ v
        cont : maybe type → type → spanM ⊤
        cont nothing tp = check-term t nothing ≫=span λ m → 
                       get-ctxt λ Γ →
                       spanM-add (Theta-span Γ pi (AbstractVars vs) t ls checking
                                    [ expected-type Γ tp ] (just ("We could not compute a motive from the given term"
                                                                     ^ " because one of the abstracted vars is not in scope.")))
        cont (just motive) tp =
           get-ctxt λ Γ →
            spanM-add (Theta-span Γ pi (AbstractVars vs) t ls checking (expected-type Γ tp :: [ the-motive Γ motive ]) nothing) ≫span 
            check-term (lterms-to-term Abstract (AppTp t (NoSpans motive (posinfo-plus (term-end-pos t) 1))) ls)
               (just tp)
        {-rep-var : ctxt → var → trie term → trie term
        rep-var Γ v ρ with trie-lookup (ctxt-get-qualif Γ) v
        ...| nothing = ρ
        ...| just (v' , _) = trie-insert ρ v' (Var posinfo-gen v)
        rep-vars : ctxt → vars → trie term → trie term
        rep-vars Γ (VarsStart v) = rep-var Γ v
        rep-vars Γ (VarsNext v vs) ρ = rep-vars Γ vs (rep-var Γ v ρ)-}

check-termi (Hole pi) tp =
  get-ctxt λ Γ → spanM-add (hole-span Γ pi tp []) ≫span return-when tp tp

check-termi (IotaPair pi t1 t2 og pi') (just tp) = -- (Iota pi1 pi2 x tp1 tp2)) =
  get-ctxt λ Γ → case hnf Γ (unfolding-elab unfold-head) tp tt of λ where
    (Iota pi1 pi2 x tp1 tp2) →
      check-term t1 (just tp1) ≫span
      let t1' = qualif-term Γ t1
          t2' = qualif-term Γ t2 in
      check-term t2 (just (subst Γ t1' x tp2)) ≫span
      optGuide-spans og checking ≫span
      check-optGuide og tp1 tp2 pi2 x ≫=span λ e →
      let cc = check-conv Γ t1' t2' e in
      spanM-add (IotaPair-span pi pi' checking (expected-type Γ (Iota pi1 pi2 x tp1 tp2) :: snd cc) (fst cc))
    tp → spanM-add (IotaPair-span pi pi' checking [ expected-type Γ tp ]
           (just "The type we are checking against is not a iota-type"))
  where ntag : ctxt → string → string → term → unfolding → tagged-val
        ntag Γ nkind which t u = to-string-tag (nkind ^ " of the " ^ which ^ " component: ") Γ (hnf Γ u t tt)
        err : ctxt → string → term → tagged-val
        err Γ which t = ntag Γ "Hnf" which t (unfolding-elab unfold-head)
        check-conv : ctxt → term → term → err-m → err-m × 𝕃 tagged-val
        check-conv Γ t1 t2 e = if conv-term Γ t1 t2
          then e , []
          else just "The two components of the iota-pair are not convertible (as required)." ,
                       err Γ "first" t1 :: [ err Γ "second" t2 ]
        check-optGuide : optGuide → type → type → posinfo → var → spanM err-m
        check-optGuide NoGuide tp1 tp2 pi2 x = spanMr nothing
        check-optGuide (Guide pi x' tp) tp1 tp2 pi2 x = get-ctxt λ Γ → with-ctxt (ctxt-term-decl pi x' tp1 Γ) (check-type tp (just (Star posinfo-gen))) ≫span
          spanMr (if conv-type Γ tp2 (qualif-type (ctxt-var-decl x Γ) (subst Γ (Var pi2 x) x' tp))
            then nothing
            else just "The expected type does not match the guided type")

check-termi (IotaPair pi t1 t2 (Guide pi' x T2) pi'') nothing =
  get-ctxt λ Γ →
  check-term t1 nothing ≫=span λ T1 →
  check-term t2 (just (qualif-type Γ (subst Γ (qualif-term Γ t1) x T2))) ≫span
  maybe-else spanMok (λ T1 → with-ctxt (ctxt-term-decl pi' x T1 Γ) (check-type T2 (just (Star posinfo-gen)))) T1 ≫span
  let T2' = qualif-type (ctxt-var-decl x Γ) T2 in
  spanM-add (IotaPair-span pi pi'' synthesizing (maybe-else [] (λ T1 → [ type-data Γ (Iota posinfo-gen posinfo-gen x T1 T2') ]) T1) nothing) ≫span
  spanM-add (Var-span (ctxt-var-decl-loc pi' x Γ) pi' x synthesizing [] nothing) ≫span
  spanMr (T1 ≫=maybe λ T1 → just (Iota posinfo-gen posinfo-gen x T1 T2'))
  where
    err : ctxt → err-m × 𝕃 tagged-val
    err Γ = if conv-term Γ t1 t2
      then nothing , []
      else just "The two components of the iota-pair are not convertible (as required)." ,
        to-string-tag "Hnf of the first component" Γ (hnf Γ unfold-head t1 tt) ::
        [ to-string-tag "Hnf of the second component" Γ (hnf Γ unfold-head t2 tt) ]

check-termi (IotaPair pi t1 t2 NoGuide pi') nothing =
  spanM-add (IotaPair-span pi pi' synthesizing [] (just "Iota pairs require a specified type when in a synthesizing position")) ≫span
  spanMr nothing


check-termi (IotaProj t n pi) mtp =
  check-term t nothing ≫=span λ mtp' → get-ctxt λ Γ → cont' mtp (posinfo-to-ℕ n) (maybe-hnf Γ mtp')
  where cont : (outer : maybe type) → ℕ → (computed : type) → spanM (check-ret outer)
        cont mtp n computed with computed
        cont mtp 1 computed | Iota pi' pi'' x t1 t2 =
          get-ctxt λ Γ →
            spanM-add (uncurry (λ tvs → IotaProj-span t pi (maybe-to-checking mtp) (head-type Γ computed :: tvs))
                                           (check-for-type-mismatch-if Γ "synthesized" mtp t1)) ≫span
            return-when mtp (just t1)
        cont mtp 2 computed | Iota pi' pi'' x a t2 =
          get-ctxt λ Γ →
          let t2' = subst Γ (qualif-term Γ t) x t2 in
          spanM-add (uncurry (λ tvs → IotaProj-span t pi (maybe-to-checking mtp)
                      (head-type Γ computed :: tvs)) (check-for-type-mismatch-if Γ "synthesized" mtp t2')) ≫span
          return-when mtp (just t2')
        cont mtp n computed | Iota pi' pi'' x t1 t2 =
          get-ctxt λ Γ →
          spanM-add (IotaProj-span t pi (maybe-to-checking mtp) [ head-type Γ computed ] (just "Iota-projections must use .1 or .2 only.")) ≫span return-when mtp mtp
        cont mtp n computed | _ =
          get-ctxt λ Γ →
          spanM-add (IotaProj-span t pi (maybe-to-checking mtp) [ head-type Γ computed ] (just "The head type is not a iota-abstraction.")) ≫span return-when mtp mtp
        cont' : (outer : maybe type) → ℕ → (computed : maybe type) → spanM (check-ret outer)
        cont' mtp _ nothing = spanM-add (IotaProj-span t pi (maybe-to-checking mtp) [] nothing) ≫span return-when mtp mtp
        cont' mtp n (just tp) = get-ctxt λ Γ → cont mtp n (hnf Γ (unfolding-elab unfold-head) tp tt)
                                                     -- we are looking for iotas in the bodies of rec defs

check-termi (Mu pi pi' x t Tₘ pi'' cs pi''') = check-mu pi pi' (just x) t NoTerm Tₘ pi'' cs pi'''
check-termi (Mu' pi ot t Tₘ pi'' cs pi''') = check-mu pi pi-gen nothing t ot Tₘ pi'' cs pi'''

{-check-termi t tp = get-ctxt (λ Γ → spanM-add (unimplemented-term-span Γ (term-start-pos t) (term-end-pos t) tp) ≫span unimplemented-if tp)-}

-- END check-term
-- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

-- check-term-spine
-- ==================================================

-- check-term-spine is where metavariables are generated and solved, so it
-- requires its set of helpers

check-term-spine-return : ctxt → meta-vars → decortype → ℕ → spanM (maybe spine-data)
check-term-spine-return Γ Xs dt locl = spanMr (just (mk-spine-data Xs dt locl))

-- a flag indicating how aggresively we should be unfolding during matching.
-- "both" is the backtracking flag. We will attempt "both" matches, which means
-- first matching without unfolding, then if that fails unfolding the type once
-- and continue matching the subexpresions with "both"
data match-unfolding-state : Set where
  match-unfolding-both match-unfolding-approx match-unfolding-hnf : match-unfolding-state

-- main matching definitions
-- --------------------------------------------------

-- NOTE: these functions don't actually ever emit spans
match-types : meta-vars → local-vars → match-unfolding-state → (tpₓ tp : type) → spanM $ match-error-t meta-vars
match-kinds : meta-vars → local-vars → match-unfolding-state → (kₓ k : kind) → spanM $ match-error-t meta-vars
match-tks   : meta-vars → local-vars → match-unfolding-state → (tkₓ tk : tk) → spanM $ match-error-t meta-vars

record match-prototype-data : Set where
  constructor mk-match-prototype-data
  field
    match-proto-mvars : meta-vars
    match-proto-dectp : decortype
    match-proto-error : 𝔹
open match-prototype-data
match-prototype : (Xs : meta-vars) (is-hnf : 𝔹) (tp : type) (pt : prototype) → spanM $ match-prototype-data

-- substitutions used during matching
-- --------------------------------------------------

-- These have to be in the spanM monad because substitution can unlock a `stuck`
-- decoration, causing another round of prototype matching (which invokes type matching)

substh-decortype : {ed : exprd} → ctxt → renamectxt → trie ⟦ ed ⟧ → decortype → spanM $ decortype
substh-decortype Γ ρ σ (decor-type tp) = spanMr $ decor-type (substh-type Γ ρ σ tp)
substh-decortype Γ ρ σ (decor-arrow e? dom cod) =
  substh-decortype Γ ρ σ cod
  ≫=span λ cod → spanMr $ decor-arrow e? (substh-type Γ ρ σ dom) cod
  -- spanMr $ decor-arrow e? (substh-type Γ ρ σ dom) (substh-decortype Γ ρ σ cod)
substh-decortype Γ ρ σ (decor-decor e? pi x tk sol dt) =
  let x' = subst-rename-var-if Γ ρ x σ
      Γ' = ctxt-var-decl-loc pi x' Γ
      ρ' = renamectxt-insert ρ x x'
  in substh-decortype Γ' ρ' σ dt
  ≫=span λ dt' → spanMr $ decor-decor e? pi x' (substh-tk Γ ρ σ tk) (substh-meta-var-sort Γ ρ σ sol) dt'
  -- decor-decor e? x' (substh-meta-var-sol Γ' ρ' σ sol) (substh-decortype Γ' ρ' σ dt)
substh-decortype Γ ρ σ (decor-stuck tp pt) =
  match-prototype meta-vars-empty ff (substh-type Γ ρ σ tp) pt
  -- NOTE: its an invariant that if you start with no meta-variables, prototype matching
  -- produces no meta-variables as output
  ≫=span λ ret → spanMr (match-proto-dectp ret)

substh-decortype Γ ρ σ (decor-error tp pt) =
  spanMr $ decor-error (substh-type Γ ρ σ tp) pt

subst-decortype : {ed : exprd} → ctxt → ⟦ ed ⟧ → var → decortype → spanM $ decortype
subst-decortype Γ s x dt = substh-decortype Γ empty-renamectxt (trie-single x s) dt

meta-vars-subst-decortype' : (unfold : 𝔹) → ctxt → meta-vars → decortype → spanM decortype
meta-vars-subst-decortype' uf Γ Xs dt =
  substh-decortype Γ empty-renamectxt (meta-vars-get-sub Xs) dt
  ≫=span λ dt' → spanMr $
    if uf then hnf-decortype Γ (unfolding-elab unfold-head) dt' tt else dt'

meta-vars-subst-decortype : ctxt → meta-vars → decortype → spanM decortype
meta-vars-subst-decortype = meta-vars-subst-decortype' tt


-- unfolding a decorated type to reveal a term / type abstraction
-- --------------------------------------------------

{-# TERMINATING #-}
meta-vars-peel' : ctxt → span-location → meta-vars → decortype → spanM $ (𝕃 meta-var) × decortype
meta-vars-peel' Γ sl Xs (decor-decor e? pi x _ (meta-var-tp k mtp) dt) =
  let Y   = meta-var-fresh-tp Xs x sl (k , mtp)
      Xs' = meta-vars-add Xs Y
  in subst-decortype Γ (meta-var-to-type-unsafe Y) x dt
  ≫=span λ dt' → meta-vars-peel'  Γ sl Xs' dt'
  ≫=span λ ret → let Ys = fst ret ; rdt = snd ret
  in spanMr $ Y :: Ys , rdt
meta-vars-peel' Γ sl Xs dt@(decor-decor e? pi x _ (meta-var-tm _ _) _) = spanMr $ [] , dt
meta-vars-peel' Γ sl Xs dt@(decor-arrow _ _ _) = spanMr $ [] , dt
-- NOTE: vv The clause below will later generate a type error vv
meta-vars-peel' Γ sl Xs dt@(decor-stuck _ _) = spanMr $ [] , dt
-- NOTE: vv The clause below is an internal error, if reached vv
meta-vars-peel' Γ sl Xs dt@(decor-type _) = spanMr $ [] , dt
meta-vars-peel' Γ sl Xs dt@(decor-error _ _) = spanMr $ [] , dt

meta-vars-unfold-tmapp' : ctxt → span-location → meta-vars → decortype → spanM $ (𝕃 meta-var × is-tmabsd?)
meta-vars-unfold-tmapp' Γ sl Xs dt =
  meta-vars-subst-decortype Γ Xs dt
  ≫=span λ dt' → meta-vars-peel' Γ sl Xs dt'
  ≫=span λ where
    (Ys , dt'@(decor-arrow e? dom cod)) →
      spanMr $ Ys , yes-tmabsd dt' e? "_" dom ff cod
    (Ys , dt'@(decor-decor e? pi x _ (meta-var-tm dom _) cod)) →
      spanMr $ Ys , yes-tmabsd dt' e? x dom (is-free-in check-erased x (decortype-to-type cod)) cod
    (Ys , dt@(decor-decor _ _ _ _ (meta-var-tp _ _) _)) →
      spanMr $ Ys , not-tmabsd dt
-- NOTE: vv this is a type error vv
    (Ys , dt@(decor-stuck _ _)) →
      spanMr $ Ys , not-tmabsd dt
-- NOTE: vv this is an internal error, if reached vv
    (Ys , dt@(decor-type _)) →
      spanMr $ Ys , not-tmabsd dt
    (Ys , dt@(decor-error _ _)) →
      spanMr $ Ys , not-tmabsd dt

meta-vars-unfold-tpapp' : ctxt → meta-vars → decortype → spanM is-tpabsd?
meta-vars-unfold-tpapp' Γ Xs dt =
  meta-vars-subst-decortype Γ Xs dt
  ≫=span λ where
   (dt″@(decor-decor e? pi x _ (meta-var-tp k mtp) dt')) →
    spanMr $ yes-tpabsd dt″ e? x k (flip maybe-map mtp meta-var-sol.sol) dt'
   (dt″@(decor-decor _ _ _ _ (meta-var-tm _ _) _)) →
    spanMr $ not-tpabsd dt″
   (dt″@(decor-arrow _ _ _)) → spanMr $ not-tpabsd dt″
   (dt″@(decor-stuck _ _)) → spanMr $ not-tpabsd dt″
   (dt″@(decor-type _)) → spanMr $ not-tpabsd dt″
   (dt″@(decor-error _ _)) → spanMr $ not-tpabsd dt″



-- errors
-- --------------------------------------------------

-- general type errors for applications
module check-term-app-tm-errors
  {A : Set} (t₁ t₂ : term) (htp : type) (Xs : meta-vars) (is-locale : 𝔹) (m : checking-mode)
  where

  inapplicable : maybeErased → decortype → prototype → spanM (maybe A)
  inapplicable e? dt pt =
    get-ctxt λ Γ → spanM-add
      (App-span is-locale t₁ t₂ m
        (head-type Γ (meta-vars-subst-type Γ Xs htp)
          -- :: decortype-data Γ dt
          -- :: prototype-data Γ pt
          :: meta-vars-data-all Γ Xs)
        (just $ "The type of the head does not allow the head to be applied to "
         ^ h e? ^ " argument"))
    ≫span spanMr nothing
    where h : maybeErased → string
          h Erased = "an erased term"
          h NotErased = "a term"

  bad-erasure : maybeErased → spanM (maybe A)
  bad-erasure e? =
    get-ctxt λ Γ → spanM-add
      (App-span is-locale t₁ t₂ m
        (head-type Γ (meta-vars-subst-type Γ Xs htp) :: meta-vars-data-all Γ Xs)
        (just (msg e?)))
    ≫span spanMr nothing
    where
    msg : maybeErased → string
    msg Erased =
      "The type computed for the head requires an explicit (non-erased) argument,"
      ^ " but the application is marked as erased"
    msg NotErased =
      "The type computed for the head requires an implicit (erased) argument,"
      ^ " but the application is marked as not erased"

  unmatchable : (tpₓ tp : type) (msg : string) → 𝕃 tagged-val → spanM (maybe A)
  unmatchable tpₓ tp msg tvs =
    get-ctxt λ Γ → spanM-add
      (App-span is-locale t₁ t₂ m
        (arg-exp-type Γ tpₓ :: arg-type Γ tp :: tvs ++ meta-vars-data-all Γ Xs)
        (just msg))
    ≫span spanMr nothing

  unsolved-meta-vars : type → 𝕃 tagged-val → spanM (maybe A)
  unsolved-meta-vars tp tvs =
    get-ctxt λ Γ → spanM-add
      (App-span tt t₁ t₂ m
        (type-data Γ tp :: meta-vars-data-all Γ Xs ++ tvs)
        (just "There are unsolved meta-variables in this maximal application"))
    ≫span spanMr nothing

module check-term-app-tp-errors
  {A : Set} (t : term) (tp htp : type) (Xs : meta-vars) (m : checking-mode)
  where

  inapplicable : decortype → spanM (maybe A)
  inapplicable dt =
    get-ctxt λ Γ → spanM-add
      (AppTp-span t tp synthesizing
        (head-type Γ (meta-vars-subst-type Γ Xs htp)
          -- :: decortype-data Γ dt
          :: meta-vars-data-all Γ Xs)
        (just "The type of the head does not allow the head to be applied to a type argument"))
    ≫span spanMr nothing

  ctai-disagree : (ctai-sol : type) → spanM $ maybe A
  ctai-disagree ctai-sol =
    get-ctxt λ Γ → spanM-add (AppTp-span t tp m
      (head-type Γ (meta-vars-subst-type Γ Xs htp)
        :: contextual-type-argument Γ ctai-sol
        :: meta-vars-data-all Γ Xs)
      (just "The given and contextually inferred type argument differ"))
    ≫span spanMr nothing

-- meta-variable locality
-- --------------------------------------------------

-- for debugging -- prepend to the tvs returned by check-spine-locality if you're having trouble
private
  locale-tag : ℕ → tagged-val
  locale-tag n = "locale n" , [[ ℕ-to-string n ]] , []

private
  is-locale : (max : 𝔹) → (locl : maybe ℕ) → 𝔹
  is-locale max locl = max || maybe-else' locl ff iszero

check-spine-locality : ctxt → meta-vars → type → (max : 𝔹) → (locl : ℕ)
                       → spanM (maybe (meta-vars × ℕ × 𝔹))
check-spine-locality Γ Xs tp max locl =
  let new-locl  = if iszero locl then num-arrows-in-type Γ tp else locl
      new-Xs    = if iszero locl then meta-vars-empty else Xs
      left-locl = is-locale max (just locl)
  in if left-locl && (~ meta-vars-solved? Xs)
        then spanMr nothing
     else spanMr (just (new-Xs , new-locl , left-locl))


-- main definition
--------------------------------------------------

data check-term-app-ret : Set where
  check-term-app-return : (Xs : meta-vars) (cod : decortype) (arg-mode : checking-mode) → (tvs : 𝕃 tagged-val) → check-term-app-ret

check-term-app : (Xs : meta-vars) (Ys : 𝕃 meta-var) → (t₁ t₂ : term) → is-tmabsd → 𝔹 → spanM (maybe check-term-app-ret)

check-term-spine t'@(App t₁ e? t₂) pt max =
  -- 1) type the applicand, extending the prototype
    let pt' = proto-arrow e? pt in
    check-term-spine t₁ pt' ff
      on-fail handleApplicandTypeError
  -- 2) make sure the applicand type reveals an arrow (term abstraction)
  ≫=spanm' λ ret → let (mk-spine-data Xs dt locl) = ret in
    -- the meta-vars need to know the span they were introduced in
    get-ctxt λ Γ  → let sloc = span-loc $ ctxt-get-current-filename Γ in
    -- see if the decorated type of the head `dt` reveals an arrow
    meta-vars-unfold-tmapp' Γ sloc Xs dt
  ≫=span λ ret → let Ys = fst ret ; tm-arrow? = snd ret in
    spanMr tm-arrow? on-fail (λ _ → genInapplicableError Xs dt pt' locl)
    -- if so, get the (plain, undecorated) type of the head `htp`
  ≫=spans' λ arr → let htp = decortype-to-type ∘ is-tmabsd-dt $ arr in
  -- 3) make sure erasures of the applicand type + syntax of application match
    checkErasuresMatch e? (is-tmabsd-e? arr) htp Xs locl
  -- 4) type the application, filling in missing type arguments with meta-variables
  ≫=spanm' λ _ → check-term-app Xs Ys t₁ t₂ arr (islocl locl)
  -- 5) check no unsolved mvars, if the application is maximal (or a locality)
  ≫=spanm' λ {(check-term-app-return Xs' rtp' arg-mode tvs) →
    let rtp = decortype-to-type rtp' in
    checkLocality Γ Xs' htp rtp max (pred locl) tvs
  ≫=spanm' uncurry₂ λ Xs'' locl' is-loc →
  -- 6) generate span and finish
    genAppSpan Γ Xs Xs' Ys pt rtp is-loc tvs
  ≫span check-term-spine-return Γ Xs'' rtp' locl'
  }

  where
  mode = prototype-to-checking pt

  expected-type-if-pt : ctxt → prototype → 𝕃 tagged-val
  expected-type-if-pt Γ pt = case pt of λ where
    (proto-maybe mt) → maybe-else [] (λ tp → [ expected-type Γ tp ]) mt
    (proto-arrow _ _) → []

  span-loc : (fn : string) → span-location
  span-loc fn = fn , term-start-pos t₁ , term-end-pos t₂

  islocl : ℕ → 𝔹
  islocl locl = is-locale max (just $ pred locl)

  handleApplicandTypeError : spanM ∘ maybe $ _
  handleApplicandTypeError = get-ctxt λ Γ →
      spanM-add (App-span max t₁ t₂ mode (expected-type-if-pt Γ pt) nothing)
    ≫span check-term t₂ nothing
    ≫=span (const $ spanMr nothing)

  genInapplicableError : meta-vars → decortype → prototype → (locl : ℕ) → spanM (maybe _)
  genInapplicableError Xs dt pt locl =
    check-term-app-tm-errors.inapplicable
      t₁ t₂ (decortype-to-type dt) Xs (islocl locl) mode e? dt (proto-arrow e? pt)

  checkErasuresMatch : (e?₁ e?₂ : maybeErased) → type → meta-vars → (locl : ℕ) → spanM ∘ maybe $ ⊤
  checkErasuresMatch e?₁ e?₂ htp Xs locl =
    if ~ eq-maybeErased e?₁ e?₂
      then check-term-app-tm-errors.bad-erasure t₁ t₂ htp Xs (islocl locl) mode e?₁
    else (spanMr ∘ just $ triv)

  checkLocality : ctxt → meta-vars → (htp rtp : type) → (max : 𝔹) (locl : ℕ) → 𝕃 tagged-val → spanM ∘ maybe $ _
  checkLocality Γ Xs htp rtp max locl tvs =
    check-spine-locality Γ Xs rtp max locl
      on-fail check-term-app-tm-errors.unsolved-meta-vars
        t₁ t₂ htp Xs (islocl locl) mode rtp tvs
    ≫=spanm' (spanMr ∘ just)

  genAppSpan : ctxt → (Xs Xs' : meta-vars) → (Ys : 𝕃 meta-var) → prototype → type → (is-locl : 𝔹) → 𝕃 tagged-val → spanM ⊤
  genAppSpan Γ Xs Xs' Ys pt rtp is-loc tvs =
    spanM-add $ (flip uncurry)
      (meta-vars-check-type-mismatch-if (prototype-to-maybe pt) Γ "synthesized" meta-vars-empty rtp)
      λ tvs' → App-span is-loc t₁ t₂ mode
        (tvs' ++ meta-vars-intro-data Γ (meta-vars-from-list Ys)
          ++ meta-vars-sol-data Γ Xs Xs' ++ tvs)

check-term-spine t'@(AppTp t tp) pt max = get-ctxt λ Γ →
  -- 1) type the applicand
    check-term-spine t pt max
      on-fail handleApplicandTypeError
  ≫=spanm' λ ret → let (mk-spine-data Xs dt locl) = ret ; htp = decortype-to-type dt in
  -- 2) make sure it reveals a type abstraction
    meta-vars-unfold-tpapp' Γ Xs dt
     on-fail (λ _ → genInapplicableError Xs htp dt)
  -- 3) ensure the type argument has the expected kind,
  --    but don't compare with the contextually infered type argument (for now)
  ≫=spans' λ ret → let mk-tpabsd dt e? x k sol rdt = ret in
    check-type tp (just (meta-vars-subst-kind Γ Xs k))
  -- 4) produce the result type of the application
  ≫span subst-decortype-if Γ Xs x k sol rdt
  ≫=span λ ret → let Xs = fst ret ; rdt = snd ret ; rtp = decortype-to-type rdt in
  -- 5) generate span data and finish
    genAppTpSpan Γ Xs pt rtp
  ≫span check-term-spine-return Γ Xs rdt locl

  where
  mode = prototype-to-checking pt

  span-loc : ctxt → span-location
  span-loc Γ = (ctxt-get-current-filename Γ) , term-start-pos t , type-end-pos tp

  handleApplicandTypeError : spanM ∘ maybe $ spine-data
  handleApplicandTypeError =
      spanM-add (AppTp-span t tp synthesizing [] nothing)
    ≫span check-type tp nothing
    ≫=span (const $ spanMr nothing)

  genInapplicableError : meta-vars → type → decortype → spanM ∘ maybe $ spine-data
  genInapplicableError Xs htp dt =
    check-term-app-tp-errors.inapplicable t tp htp Xs mode dt

  subst-decortype-if : ctxt → meta-vars → var → kind → maybe type → decortype → spanM (meta-vars × decortype)
  subst-decortype-if Γ Xs x k sol rdt =
    if ~ is-hole tp
      then subst-decortype Γ (qualif-type Γ tp) x rdt ≫=span (λ res → spanMr (Xs , res))
      else let sol = maybe-map (λ t → mk-meta-var-sol t checking) sol
               Y   = meta-var-fresh-tp Xs x (span-loc Γ) (k , sol)
               Xs' = meta-vars-add Xs Y
           in subst-decortype Γ (meta-var-to-type-unsafe Y) x rdt ≫=span λ rdt' → spanMr (Xs' , rdt')

  genAppTpSpan : ctxt → meta-vars → prototype → (ret-tp : type) → spanM ⊤
  genAppTpSpan Γ Xs pt ret-tp = spanM-add ∘ (flip uncurry)
    -- check for a type mismatch, if there even is an expected type
    (meta-vars-check-type-mismatch-if (prototype-to-maybe pt) Γ "synthesizing" Xs ret-tp) $
    -- then take the generated 𝕃 tagged-val and add to the span
    λ tvs → AppTp-span t tp mode $ tvs ++ meta-vars-data-all Γ Xs -- ++ (prototype-data Γ tp :: [ decortype-data Γ dt ])

check-term-spine (Parens _ t _) pt max =
  check-term-spine t pt max

check-term-spine t pt max =
  check-term t nothing
  ≫=spanm' λ htp → get-ctxt λ Γ →
  let locl = num-arrows-in-type Γ htp
  in match-prototype meta-vars-empty ff htp pt
  -- NOTE: it is an invariant that the variables solved in the
  -- solution set of the fst of this are a subset of the variables given
  -- to match-* -- that is, for (σ , W) = match-prototype ...
  -- we have dom(σ) = ∅
  ≫=span λ ret → let dt = match-proto-dectp ret in
  check-term-spine-return Γ meta-vars-empty dt locl

-- check-term-app
-- --------------------------------------------------
--
-- If `dom` has unsolved meta-vars in it, synthesize argument t₂ and try to solve for them.
-- Otherwise, check t₂ against a fully known expected type
check-term-app Xs Zs t₁ t₂ (mk-tmabsd dt e? x dom occurs cod) is-locl =
   get-ctxt λ Γ → let Xs' = meta-vars-add* Xs Zs ; tp = decortype-to-type dt in
  -- 1) calculate return type of function (possible subst)
   genAppRetType Γ
  -- 2) either synth or check arg type, depending on available info
  --    checking "exits early", as well as failure
  ≫=span λ rdt → checkArgWithMetas Xs' tp rdt
    exit-early spanMr
  -- 3) match *synthesized* type with expected (partial) type
  ≫=spans' λ atp → match-types Xs' empty-trie match-unfolding-both dom atp
  ≫=span (handleMatchResult Xs' atp tp rdt)

  where
  mode = synthesizing

  genAppRetType : ctxt → spanM decortype
  genAppRetType Γ = if occurs then subst-decortype Γ (qualif-term Γ t₂) x cod else spanMr cod

  genAppRetTypeHole : ctxt → spanM decortype
  genAppRetTypeHole Γ = if occurs then subst-decortype Γ (Hole posinfo-gen) x cod else spanMr cod

  checkArgWithMetas : meta-vars → type → decortype → spanM $ (maybe check-term-app-ret ∨ type)
  checkArgWithMetas Xs' tp rdt = get-ctxt λ Γ →
    -- check arg against fully known type
    if ~ meta-vars-are-free-in-type Xs' dom
      then check-term t₂ (just dom)
          ≫span (spanMr ∘' inj₁ ∘' just $ check-term-app-return Xs' rdt mode [])
    -- synthesize type for the argument
      else check-term t₂ nothing
     -- if that doesn't work, press on -- feeding a hole for the dependency, if needed
          on-fail (genAppRetTypeHole Γ
                  ≫=span λ rdt-hole → spanMr ∘' inj₁ ∘' just $
                    check-term-app-return Xs' rdt-hole mode [ arg-exp-type Γ dom ])
        ≫=spanm' λ tp → spanMr ∘' inj₂ $ tp

  handleMatchResult : meta-vars → (atp tp : type) → decortype → match-error-t meta-vars → spanM ∘ maybe $ check-term-app-ret
  handleMatchResult Xs' atp tp rdt (match-error (msg , tvs)) =
    check-term-app-tm-errors.unmatchable
      t₁ t₂ tp Xs' is-locl mode dom atp msg tvs
  handleMatchResult Xs' atp tp rdt (match-ok Xs) = get-ctxt λ Γ →
      meta-vars-subst-decortype' ff Γ Xs rdt
    ≫=span λ rdt → spanMr ∘ just $ check-term-app-return Xs rdt mode []

match-unfolding-next : match-unfolding-state → match-unfolding-state
match-unfolding-next match-unfolding-both = match-unfolding-both
match-unfolding-next match-unfolding-approx = match-unfolding-approx
match-unfolding-next match-unfolding-hnf = match-unfolding-both

module m-err = meta-vars-match-errors

check-type-for-match : type → spanM $ match-error-t kind
check-type-for-match tp =
  (with-qualified-qualif $ with-clear-error $ get-ctxt λ Γ →
      check-type tp nothing
        on-fail spanMr ∘ match-error $ "Could not kind computed arg type" , []
    ≫=spanm' λ k → spanMr ∘ match-ok $ k)
  ≫=spand spanMr
  where
  -- helper to restore qualif state
  with-qualified-qualif : ∀ {A} → spanM A → spanM A
  with-qualified-qualif sm =
    get-ctxt λ Γ → with-ctxt (qualified-ctxt Γ) sm

  -- helper to restore error state
  with-clear-error : ∀ {A} → spanM A → spanM A
  with-clear-error m =
      get-error λ es → set-error nothing
    ≫span m
    ≫=span λ a → set-error es
    ≫span spanMr a

-- match-types
-- --------------------------------------------------

match-types-ok : meta-vars → spanM $ match-error-t meta-vars
match-types-ok = spanMr ∘ match-ok

match-types-error : match-error-data → spanM $ match-error-t meta-vars
match-types-error = spanMr ∘ match-error

match-types Xs Ls match-unfolding-both tpₓ tp =
    get-ctxt λ Γ →
    match-types Xs Ls match-unfolding-approx tpₓ tp
  ≫=span λ where
    (match-ok Xs) → match-types-ok Xs
    (match-error msg) →
      match-types Xs Ls match-unfolding-hnf
        (hnf Γ (unfolding-elab unfold-head) tpₓ tt)
        (hnf Γ (unfolding-elab unfold-head) tp tt)

match-types Xs Ls unf tpₓ@(TpVar pi x) tp =
  -- check that x is a meta-var
  get-ctxt λ Γ →
  maybe-else' (meta-vars-lookup-with-kind Xs x)
    -- if not, make sure the two variables are the same
    -- TODO: above assumes no term meta-variables
    (spanMr (err⊎-guard (~ conv-type Γ tpₓ tp) m-err.e-match-failure
            ≫⊎ match-ok Xs))
  -- scope check the solution
  λ ret → let X = fst ret ; kₓ = snd ret in
  if are-free-in-type check-erased Ls tp then
    match-types-error $ m-err.e-meta-scope Γ tpₓ tp
  else (check-type-for-match tp
  ≫=spans' λ k → match-kinds Xs empty-trie match-unfolding-both kₓ k
    on-fail (λ _ → spanMr ∘ match-error $ m-err.e-bad-sol-kind Γ x tp)
  ≫=spans' λ Xs → spanMr (meta-vars-solve-tp Γ Xs x tp synthesizing)
  ≫=spans' λ Xs → match-types-ok $ meta-vars-update-kinds Γ Xs Xs)

match-types Xs Ls unf (TpApp tpₓ₁ tpₓ₂) (TpApp tp₁ tp₂) =
    match-types Xs Ls unf tpₓ₁ tp₁
  ≫=spans' λ Xs' → match-types Xs' Ls (match-unfolding-next unf) tpₓ₂ tp₂

match-types Xs Ls unf (TpAppt tpₓ tmₓ) (TpAppt tp tm) =
    match-types Xs Ls unf tpₓ tp
  ≫=spans' λ Xs' → get-ctxt λ Γ →
    spanMr $ if ~ conv-term Γ tmₓ tm
      then (match-error m-err.e-match-failure) else
    match-ok Xs'

match-types Xs Ls unf tpₓ'@(Abs piₓ bₓ piₓ' xₓ tkₓ tpₓ) tp'@(Abs pi b pi' x tk tp) =
  get-ctxt λ Γ →
  if ~ eq-maybeErased bₓ b
    then (match-types-error m-err.e-match-failure) else
  ( match-tks Xs Ls (match-unfolding-next unf) tkₓ tk
  ≫=spans' λ Xs' → with-ctxt (Γ→Γ' Γ) 
    (match-types Xs' Ls' (match-unfolding-next unf) tpₓ tp))
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)
  Ls' = stringset-insert Ls x

match-types Xs Ls unf tpₓ@(TpArrow tp₁ₓ atₓ tp₂ₓ) tp@(TpArrow tp₁ at tp₂) =
  get-ctxt λ Γ → if ~ eq-maybeErased atₓ at
    then match-types-error m-err.e-match-failure else
  ( match-types Xs Ls (match-unfolding-next unf) tp₁ₓ tp₁
  ≫=spans' λ Xs → match-types Xs Ls (match-unfolding-next unf) tp₂ₓ tp₂)

match-types Xs Ls unf tpₓ@(TpArrow tp₁ₓ atₓ tp₂ₓ) tp@(Abs pi b pi' x (Tkt tp₁) tp₂) =
  get-ctxt λ Γ → if ~ eq-maybeErased atₓ b
    then match-types-error m-err.e-match-failure else
  ( match-types Xs Ls (match-unfolding-next unf) tp₁ₓ tp₁
  ≫=spans' λ Xs → match-types Xs (stringset-insert Ls x) (match-unfolding-next unf) tp₂ₓ tp₂)

match-types Xs Ls unf tpₓ@(Abs piₓ bₓ piₓ' xₓ (Tkt tp₁ₓ) tp₂ₓ) tp@(TpArrow tp₁ at tp₂) =
  get-ctxt λ Γ → if ~ eq-maybeErased bₓ at
    then match-types-error m-err.e-match-failure else
  ( match-types Xs Ls (match-unfolding-next unf) tp₁ₓ tp₁
  ≫=spans' λ Xs → match-types Xs (stringset-insert Ls xₓ) (match-unfolding-next unf) tp₂ₓ tp₂)

match-types Xs Ls unf (Iota _ piₓ xₓ mₓ tpₓ) (Iota _ pi x m tp) =
  get-ctxt λ Γ → match-types Xs Ls (match-unfolding-next unf) mₓ m
  ≫=spans' λ Xs → with-ctxt (Γ→Γ' Γ)
    (match-types Xs Ls' (match-unfolding-next unf) tpₓ tp)
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)
  Ls' = stringset-insert Ls x

match-types Xs Ls unf (TpEq _ t₁ₓ t₂ₓ _) (TpEq _ t₁ t₂ _) =
  get-ctxt λ Γ → if ~ conv-term Γ t₁ₓ t₁
    then match-types-error $ m-err.e-match-failure else
  if ~ conv-term Γ t₂ₓ t₂
    then match-types-error $ m-err.e-match-failure else
  match-types-ok Xs

match-types Xs Ls unf (Lft _ piₓ xₓ tₓ lₓ) (Lft _ pi x t l) =
  get-ctxt λ Γ → if ~ conv-liftingType Γ lₓ l
    then match-types-error $ m-err.e-match-failure else
  if ~ conv-term (Γ→Γ' Γ) tₓ t
    then match-types-error $ m-err.e-match-failure else
  match-types-ok Xs
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)

match-types Xs Ls unf (TpLambda _ piₓ xₓ atkₓ tpₓ) (TpLambda _ pi x atk tp) =
  get-ctxt λ Γ → match-tks Xs Ls (match-unfolding-next unf) atkₓ atk
  ≫=spans' λ Xs → with-ctxt (Γ→Γ' Γ)
  (match-types Xs Ls' (match-unfolding-next unf) tpₓ tp)
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)
  Ls' = stringset-insert Ls x

match-types Xs Ls unf (NoSpans tpₓ _) (NoSpans tp _) =
  match-types Xs Ls unf tpₓ tp

-- TODO for now, don't approximate lets
match-types Xs Ls unf (TpLet piₓ (DefTerm pi x ot t) tpₓ) tp =
  get-ctxt λ Γ → match-types Xs Ls unf (subst Γ (Chi posinfo-gen ot t) x tpₓ) tp

match-types Xs Ls unf (TpLet piₓ (DefType pi x k tpₓ-let) tpₓ) tp =
  get-ctxt λ Γ → match-types Xs Ls unf (subst Γ tpₓ-let x tpₓ) tp

match-types Xs Ls unf tpₓ (TpLet _ (DefTerm _ x ot t) tp) =
  get-ctxt λ Γ → match-types Xs Ls unf tpₓ (subst Γ (Chi posinfo-gen ot t) x tp)

match-types Xs Ls unf tpₓ (TpLet _ (DefType _ x k tp-let) tp) =
  get-ctxt λ Γ → match-types Xs Ls unf tpₓ (subst Γ tp-let x tp)

-- match-types Xs Ls unf (TpHole x₁) tp = {!!}

match-types Xs Ls unf (TpParens _ tpₓ _) tp =
  match-types Xs Ls unf tpₓ tp

match-types Xs Ls unf tpₓ (TpParens _ tp _) =
  match-types Xs Ls unf tpₓ tp

match-types Xs Ls unf tpₓ tp =
  get-ctxt λ Γ → match-types-error m-err.e-match-failure

-- match-kinds
-- --------------------------------------------------

-- match-kinds-norm: match already normalized kinds
match-kinds-norm : meta-vars → local-vars → match-unfolding-state → (kₓ k : kind) → spanM $ match-error-t meta-vars
match-kinds-norm Xs Ls uf (KndParens _ kₓ _) (KndParens _ k _) =
  match-kinds Xs Ls uf kₓ k

-- kind pi
match-kinds-norm Xs Ls uf (KndPi _ piₓ xₓ tkₓ kₓ) (KndPi _ pi x tk k) =
  get-ctxt λ Γ → match-tks Xs Ls uf tkₓ tk
  ≫=spans' λ Xs → with-ctxt (Γ→Γ' Γ)
    (match-kinds Xs Ls uf kₓ k)
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)
  Ls' = stringset-insert Ls x

-- kind arrow
match-kinds-norm Xs Ls uf (KndArrow kₓ₁ kₓ₂) (KndArrow k₁ k₂) =
  match-kinds Xs Ls uf kₓ₁ k₁
  ≫=spans' λ Xs → match-kinds Xs Ls uf kₓ₂ k₂

match-kinds-norm Xs Ls uf (KndArrow kₓ₁ kₓ₂) (KndPi _ pi x (Tkk k₁) k₂) =
  match-kinds Xs Ls uf kₓ₁ k₁
  ≫=spans' λ Xs → match-kinds Xs Ls uf kₓ₂ k₂

match-kinds-norm Xs Ls uf (KndPi _ _ x (Tkk kₓ₁) kₓ₂) (KndArrow k₁ k₂) =
  match-kinds Xs Ls uf kₓ₁ k₁
  ≫=spans' λ Xs → match-kinds Xs Ls uf kₓ₂ k₂

-- kind tp arrow
match-kinds-norm Xs Ls uf (KndTpArrow tpₓ kₓ) (KndTpArrow tp k) =
  match-types Xs Ls uf tpₓ tp
  ≫=spans' λ Xs → match-kinds Xs Ls uf kₓ k

match-kinds-norm Xs Ls uf (KndPi _ _ x (Tkt tpₓ) kₓ) (KndTpArrow tp k) =
  match-types Xs Ls uf tpₓ tp
  ≫=spans' λ Xs → match-kinds Xs Ls uf kₓ k

match-kinds-norm Xs Ls uf (KndTpArrow tpₓ kₓ) (KndPi _ _ x (Tkt tp) k) =
  match-types Xs Ls uf tpₓ tp
  ≫=spans' λ Xs → match-kinds Xs Ls uf kₓ k

match-kinds-norm Xs Ls uf (Star _) (Star _) =
  match-types-ok $ Xs
match-kinds-norm Xs Ls uf kₓ k =
  get-ctxt λ Γ → match-types-error $ m-err.e-matchk-failure -- m-err.e-kind-ineq Γ kₓ k

match-kinds Xs Ls uf kₓ k =
  get-ctxt λ Γ →
  match-kinds-norm Xs Ls uf
    (hnf Γ (unfolding-elab unfold-head) kₓ tt)
    (hnf Γ (unfolding-elab unfold-head) k tt)

-- match-tk
-- --------------------------------------------------
match-tks Xs Ls uf (Tkk kₓ) (Tkk k) = match-kinds Xs Ls uf kₓ k
match-tks Xs Ls uf (Tkt tpₓ) (Tkt tp) = match-types Xs Ls uf tpₓ tp
match-tks Xs Ls uf tkₓ tk =
  get-ctxt λ Γ → match-types-error m-err.e-matchk-failure -- m-err.e-tk-ineq Γ tkₓ tk


-- match-prototype
-- --------------------------------------------------

match-prototype-err : type → prototype → spanM match-prototype-data
match-prototype-err tp pt = spanMr $ mk-match-prototype-data meta-vars-empty (decor-error tp pt) tt

{-
  --------------------
  Xs ⊢? T ≔ ⁇ ⇒ (∅ , T)
-}
match-prototype Xs uf tp (proto-maybe nothing) =
  spanMr $ mk-match-prototype-data Xs (decor-type tp) ff

{-
  Xs ⊢= T ≔ S ⇒ σ
  --------------------
  Xs ⊢? T ≔ S ⇒ (σ , T)
-}
match-prototype Xs uf tp pt@(proto-maybe (just tp')) =
  match-types Xs empty-trie match-unfolding-both tp tp'
    on-fail (λ _ → spanMr $ mk-match-prototype-data Xs (decor-error tp pt) tt)
  ≫=spans' λ Xs' → spanMr $ mk-match-prototype-data Xs' (decor-type tp) ff

{-
  Xs,X ⊢? T ≔ ⁇ → P ⇒ (σ , W)
  -----------------------------------------------
  Xs ⊢? ∀ X . T ≔ ⁇ → P ⇒ (σ - X , ∀ X = σ(X) . W)
-}
match-prototype Xs uf (Abs pi bₓ pi' x (Tkk k) tp) pt'@(proto-arrow e? pt) =
  get-ctxt λ Γ →
  -- 1) generate a fresh meta-var Y, add it to the meta-vars, and rename
  --    occurences of x in tp to Y
  let ret = meta-vars-add-from-tpabs Γ missing-span-location Xs (mk-tpabs Erased x k tp)
      Y = fst ret ; Xs' = snd ret ; tp' = subst Γ (meta-var-to-type-unsafe Y) x tp
  -- 2) match the body against the original prototype to generate a decorated type
  --    and find some solutions
  in match-prototype Xs' ff tp' pt'
  ≫=span λ ret →
  let mk-match-prototype-data Xs' dt err = ret
      Y' = maybe-else' (meta-vars-lookup Xs' (meta-var-name Y)) Y λ Y → Y
  -- 3) replace the meta-vars with the bound type variable
  in subst-decortype Γ (TpVar pi x) (meta-var-name Y) dt
  -- 4) leave behind the solution for Y as a decoration and drop Y from Xs
  ≫=span λ dt' →
  let sort' = meta-var.sort (meta-var-set-src Y' checking)
      dt″ = decor-decor Erased pi x (Tkk k) sort' dt' in
  spanMr $ mk-match-prototype-data (meta-vars-remove Xs' Y) dt″ err

{-
  Xs ⊢? T ≔ P ⇒ (σ , P)
  -----------------------------
  Xs ⊢? S → T ≔ ⁇ → P ⇒ (σ , P)
-}
match-prototype Xs uf (Abs pi b pi' x (Tkt dom) cod) (proto-arrow e? pt) =
  match-prototype Xs ff cod pt
  ≫=span λ ret →
  let mk-match-prototype-data Xs dt err = ret
      dt' = decor-decor b pi x (Tkt dom) (meta-var-tm dom nothing) dt
  in spanMr $ if ~ eq-maybeErased b e?
    then mk-match-prototype-data meta-vars-empty dt' tt
  else mk-match-prototype-data Xs dt' err

match-prototype Xs uf (TpArrow dom at cod) (proto-arrow e? pt) =
  match-prototype Xs ff cod pt
  ≫=span λ ret →
  let mk-match-prototype-data Xs' dt err = ret
      dt' = decor-arrow at dom dt
  in spanMr $ if ~ eq-maybeErased at e?
    then mk-match-prototype-data meta-vars-empty dt' tt
  else mk-match-prototype-data Xs' dt' err

{-
  X ∈ Xs
  -----------------------------------
  Xs ⊢? X ≔ ⁇ → P ⇒ (σ , (X , ⁇ → P))
-}
match-prototype Xs tt tp@(TpVar pi x) pt@(proto-arrow _ _) =
  spanMr $ mk-match-prototype-data Xs (decor-stuck tp pt) ff

-- everything else...
-- Types for which we should keep digging
match-prototype Xs ff tp@(TpVar pi x) pt@(proto-arrow _ _) =
  get-ctxt λ Γ →
  match-prototype Xs tt (hnf Γ (unfolding-elab unfold-head) tp tt) pt
match-prototype Xs uf (NoSpans tp _) pt@(proto-arrow _ _) =
  match-prototype Xs uf tp pt
match-prototype Xs uf (TpParens _ tp _) pt@(proto-arrow _ _) =
  match-prototype Xs uf tp pt
match-prototype Xs uf (TpLet pi (DefTerm piₗ x opt t) tp) pt@(proto-arrow _ _) =
  get-ctxt λ Γ →
  let tp' = subst Γ (Chi posinfo-gen opt t) x tp in
  match-prototype Xs uf tp' pt
match-prototype Xs uf (TpLet pi (DefType piₗ x k tp') tp) pt@(proto-arrow _ _) =
  get-ctxt λ Γ →
  let tp″ = subst Γ tp' x tp in
  match-prototype Xs uf tp″ pt
match-prototype Xs ff tp@(TpApp _ _) pt@(proto-arrow _ _) =
  get-ctxt λ Γ →
  match-prototype Xs tt (hnf Γ (unfolding-elab unfold-head) tp tt) pt
match-prototype Xs ff tp@(TpAppt _ _) pt@(proto-arrow _ _) =
  get-ctxt λ Γ →
  match-prototype Xs tt (hnf Γ (unfolding-elab unfold-head) tp tt) pt
-- types for which we should suspend disbelief
match-prototype Xs tt tp@(TpApp _ _) pt@(proto-arrow _ _) =
  spanMr $ mk-match-prototype-data Xs (decor-stuck tp pt) ff
match-prototype Xs tt tp@(TpAppt _ _) pt@(proto-arrow _ _) =
  spanMr $ mk-match-prototype-data Xs (decor-stuck tp pt) ff
-- types which clearly do not match the prototype
match-prototype Xs uf tp@(TpEq _ _ _ _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
match-prototype Xs uf tp@(TpHole _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
match-prototype Xs uf tp@(TpLambda _ _ _ _ _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
match-prototype Xs uf tp@(Iota _ _ _ _ _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
match-prototype Xs uf tp@(Lft _ _ _ _ _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt

-- check-typei: check a type against (maybe) a kind
-- ==================================================

--ACG WIP
--check-typei (TpHole pi) k = spanM-add
check-typei (TpHole pi) k = 
  get-ctxt (λ Γ → spanM-add (tp-hole-span Γ pi k []) ≫span return-when k k)


check-typei (TpParens pi t pi') k =
  spanM-add (punctuation-span "Parens (type)" pi pi') ≫span
  check-type t k
check-typei (NoSpans t _) k = check-type t k ≫=spand spanMr
check-typei (TpVar pi x) mk =
  get-ctxt (cont mk)
  where cont : (mk : maybe kind) → ctxt → spanM (check-ret mk) 
        cont mk Γ with ctxt-lookup-type-var Γ x
        cont mk Γ | nothing = 
          spanM-add (TpVar-span Γ pi x (maybe-to-checking mk)
                       (expected-kind-if Γ mk ++ [ missing-kind ])
                       (just "Missing a kind for a type variable.")) ≫span
          return-when mk mk
        cont nothing Γ | (just k) = 
          spanM-add (TpVar-span Γ pi x synthesizing [ kind-data Γ k ] nothing) ≫span
          check-type-return Γ k
        cont (just k) Γ | just k' = 
         spanM-add (TpVar-span Γ pi x checking
           (expected-kind Γ k :: [ kind-data Γ k' ])
           (if conv-kind Γ k k' then nothing else just "The computed kind does not match the expected kind."))
check-typei (TpLambda pi pi' x atk body) (just k) with to-absk k 
check-typei (TpLambda pi pi' x atk body) (just k) | just (mk-absk x' atk' _ k') =
   check-tk atk ≫span
   spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
   get-ctxt λ Γ' →
   add-tk pi' x atk ≫=span λ mi → 
   get-ctxt λ Γ → 
   spanM-add (if conv-tk Γ' (qualif-tk Γ' atk) atk' then
                TpLambda-span Γ pi pi' x atk body checking [ kind-data Γ' k ] nothing
              else
                uncurry (λ tvs err → TpLambda-span Γ pi pi' x atk body checking tvs (just err)) (lambda-bound-var-conv-error Γ' x atk' (qualif-tk Γ' atk) [ kind-data Γ' k ])) ≫span
   check-type body (just (rename-var Γ' x' (qualif-var Γ x) k')) ≫span
   spanM-restore-info x mi
check-typei (TpLambda pi pi' x atk body) (just k) | nothing = 
   check-tk atk ≫span
   spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
   get-ctxt λ Γ →
   spanM-add (TpLambda-span Γ pi pi' x atk body checking [ expected-kind Γ k ]
               (just "The type is being checked against a kind which is not an arrow- or Pi-kind."))

check-typei (TpLambda pi pi' x atk body) nothing =
  spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  check-type body nothing ≫=span
  cont ≫=span λ mk →
  spanM-restore-info x mi ≫span
  spanMr mk

  where cont : maybe kind → spanM (maybe kind)
        cont nothing = 
          get-ctxt λ Γ →
          spanM-add (TpLambda-span Γ pi pi' x atk body synthesizing [] nothing) ≫span
          spanMr nothing
        cont (just k) =
          get-ctxt λ Γ →
          let atk' = qualif-tk Γ atk in
          -- This should indeed "unqualify" occurrences of x in k for r
          let r = absk-tk x atk' (rename-var Γ (pi' % x) x k) in
          spanM-add (TpLambda-span Γ pi pi' x atk' body synthesizing [ kind-data Γ r ] nothing) ≫span
          spanMr (just r)

check-typei (Abs pi b {- All or Pi -} pi' x atk body) k = 
  get-ctxt λ Γ →
  spanM-add (punctuation-span "Forall" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  get-ctxt λ Γ →
  spanM-add (uncurry (TpQuant-span Γ (~ b) pi pi' x atk body (maybe-to-checking k))
               (if-check-against-star-data Γ "A type-level quantification" k)) ≫span
  check-type body (just star) ≫span
  spanM-restore-info x mi ≫span
  return-star-when k

check-typei (TpArrow t1 _ t2) k = 
  get-ctxt λ Γ →
  spanM-add (uncurry (TpArrow-span t1 t2 (maybe-to-checking k)) (if-check-against-star-data Γ "An arrow type" k)) ≫span
  check-type t1 (just star) ≫span
  check-type t2 (just star) ≫span
  return-star-when k

check-typei (TpAppt tp t) k =
  check-type tp nothing ≫=span cont'' ≫=spanr cont' k
  where cont : kind → spanM (maybe kind)
        cont (KndTpArrow tp' k') = 
          check-term t (just tp') ≫span 
          spanMr (just k')
        cont (KndPi _ _ x (Tkt tp') k') = 
          check-term t (just tp') ≫span 
          get-ctxt λ Γ → 
          spanMr (just (subst Γ (qualif-term Γ t) x k'))
        cont k' =
          get-ctxt λ Γ → 
          spanM-add (TpAppt-span tp t (maybe-to-checking k)
            (type-app-head Γ tp :: head-kind Γ k' :: [ term-argument Γ t ])
            (just ("The kind computed for the head of the type application does"
                ^ " not allow the head to be applied to an argument which is a term"))) ≫span
          spanMr nothing
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          get-ctxt λ Γ →
          spanM-add (TpAppt-span tp t synthesizing [ kind-data Γ k ] nothing) ≫span
          check-type-return Γ k
        cont' (just k') k = 
          get-ctxt λ Γ → 
          if conv-kind Γ k k'
            then spanM-add (TpAppt-span tp t checking (expected-kind Γ k' :: [ kind-data Γ k ]) nothing)
            else spanM-add (TpAppt-span tp t checking (expected-kind Γ k' :: [ kind-data Γ k ])
              (just "The kind computed for a type application does not match the expected kind."))
        cont'' : maybe kind → spanM (maybe kind)
        cont'' nothing = spanM-add (TpAppt-span tp t (maybe-to-checking k) [] nothing) ≫span spanMr nothing
        cont'' (just k) = cont k

check-typei (TpApp tp tp') k =
  check-type tp nothing ≫=span cont'' ≫=spanr cont' k
  where cont : kind → spanM (maybe kind)
        cont (KndArrow k'' k') = 
          check-type tp' (just k'') ≫span 
          spanMr (just k')
        cont (KndPi _ _ x (Tkk k'') k') = 
          check-type tp' (just k'') ≫span 
          get-ctxt λ Γ → 
          spanMr (just (subst Γ (qualif-type Γ tp') x k'))
        cont k' =
          get-ctxt λ Γ → 
          spanM-add (TpApp-span tp tp' (maybe-to-checking k)
            (type-app-head Γ tp :: head-kind Γ k' :: [ type-argument Γ tp' ])
            (just ("The kind computed for the head of the type application does"
                ^ " not allow the head to be applied to an argument which is a type"))) ≫span
          spanMr nothing
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          get-ctxt λ Γ → 
          spanM-add (TpApp-span tp tp' synthesizing [ kind-data Γ k ] nothing) ≫span
          check-type-return Γ k
        cont' (just k') k = 
          get-ctxt λ Γ → 
          if conv-kind Γ k k'
            then spanM-add (TpApp-span tp tp' checking (expected-kind Γ k' :: [ kind-data Γ k' ]) nothing)
            else spanM-add (TpApp-span tp tp' checking (expected-kind Γ k' :: [ kind-data Γ k ])
                   (just "The kind computed for a type application does not match the expected kind."))
        cont'' : maybe kind → spanM (maybe kind)
        cont'' nothing = spanM-add (TpApp-span tp tp' (maybe-to-checking k) [] nothing) ≫span spanMr nothing
        cont'' (just k) = cont k

check-typei (TpEq pi t1 t2 pi') k = 
  get-ctxt (λ Γ → 
  untyped-term-spans t1 ≫span
  set-ctxt Γ ≫span 
  untyped-term-spans t2 ≫span
  set-ctxt Γ) ≫span 
  get-ctxt λ Γ → 
  spanM-add (uncurry (TpEq-span pi t1 t2 pi' (maybe-to-checking k)) (if-check-against-star-data Γ "An equation" k)) ≫span
  -- spanM-add (unchecked-term-span t1) ≫span
  -- spanM-add (unchecked-term-span t2) ≫span
  return-star-when k

check-typei (Lft pi pi' X t l) k = 
  add-tk pi' X (Tkk star) ≫=span λ mi → 
  get-ctxt λ Γ → check-term t (just (qualif-type Γ (liftingType-to-type X l))) ≫span
  spanM-add (punctuation-span "Lift" pi (posinfo-plus pi 1)) ≫span
  spanM-restore-info X mi ≫span
  cont k (qualif-kind Γ (liftingType-to-kind l))
  where cont : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont nothing k = get-ctxt λ Γ → spanM-add (Lft-span Γ pi pi' X t synthesizing [ kind-data Γ k ] nothing) ≫span spanMr (just k)
        cont (just k') k = 
          get-ctxt λ Γ → 
          if conv-kind Γ k k' then 
              spanM-add (Lft-span Γ pi pi' X t checking ( expected-kind Γ k' :: [ kind-data Γ k ]) nothing)
            else
              spanM-add (Lft-span Γ pi pi' X t checking ( expected-kind Γ k' :: [ kind-data Γ k ]) (just "The expected kind does not match the computed kind."))
check-typei (Iota pi pi' x t1 t2) mk =
  get-ctxt λ Γ → 
  check-typei t1 (just star) ≫span
  add-tk pi' x (Tkt t1) ≫=span λ mi → 
  get-ctxt λ Γ →
  spanM-add (uncurry (Iota-span Γ pi pi' x t2 (maybe-to-checking mk)) (if-check-against-star-data Γ "A iota-type" mk)) ≫span
  check-typei t2 (just star) ≫span
  spanM-restore-info x mi ≫span
  return-star-when mk

check-typei (TpLet pi d T) mk =
  check-def d ≫=span finish
  where
  maybe-subst : defTermOrType → (mk : maybe kind) → check-ret mk → spanM (check-ret mk)
  maybe-subst _ (just k) triv = spanMok
  maybe-subst _ nothing nothing = spanMr nothing
  maybe-subst (DefTerm pi x NoType t) nothing (just k) = get-ctxt λ Γ →
    spanMr (just (subst Γ (qualif-term Γ (Chi posinfo-gen NoType t)) (pi % x) k))
  maybe-subst (DefTerm pi x (SomeType T) t) nothing (just k) = get-ctxt λ Γ →
    spanMr (just (subst Γ (qualif-term Γ (Chi posinfo-gen (SomeType T) t)) (pi % x) k))
  maybe-subst (DefType pi x k' T') nothing (just k) = get-ctxt λ Γ →
    spanMr (just (subst Γ (qualif-type Γ T') (pi % x) k))

  finish : posinfo × var × restore-def × (Σ tk λ atk → if tk-is-type atk then term else type) → spanM (check-ret mk)
  finish (pi' , x , m , atk , val) =
    get-ctxt λ Γ → 
    spanM-add (TpLet-span Γ (maybe-to-checking mk) pi pi' x atk val T [] nothing) ≫span
    check-type T mk ≫=span λ r →
    spanM-restore-info x m ≫span
    maybe-subst d mk r

check-kind (KndParens pi k pi') =
  spanM-add (punctuation-span "Parens (kind)" pi pi') ≫span
  check-kind k
check-kind (Star pi) = spanM-add (Star-span pi checking nothing)

check-kind (KndVar pi x ys) =
  get-ctxt λ Γ →
  maybe-else' (ctxt-lookup-kind-var-def-args Γ x)
    (spanM-add (KndVar-span Γ (pi , x) (kvar-end-pos pi x ys) [] checking []
        (just "Undefined kind variable")))
    λ ps-as → check-args-against-params nothing (pi , x) -- Isn't used vvvv
      (fst $ snd $ elim-pair ps-as λ ps as → subst-params-args Γ ps as star) ys
 
  {-helper (ctxt-lookup-kind-var-def-args Γ x)
  where helper : maybe (params × args) → spanM ⊤
        helper (just (ps , as)) = check-args-against-params nothing (pi , x) ps (append-args as ys)
        helper nothing = get-ctxt λ Γ →
          spanM-add (KndVar-span Γ (pi , x) (kvar-end-pos pi x ys) ParamsNil checking []
            (just "Undefined kind variable"))-}

check-kind (KndArrow k k') = 
  spanM-add (KndArrow-span k k' checking nothing) ≫span
  check-kind k ≫span
  check-kind k'
check-kind (KndTpArrow t k) = 
  spanM-add (KndTpArrow-span t k checking nothing) ≫span
  check-type t (just star) ≫span
  check-kind k
check-kind (KndPi pi pi' x atk k) = 
  spanM-add (punctuation-span "Pi (kind)" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  get-ctxt λ Γ →
  spanM-add (KndPi-span Γ pi pi' x atk k checking nothing) ≫span
  check-kind k ≫span
  spanM-restore-info x mi

check-args-against-params kind-or-import orig ps ys =
  caap (~ isJust kind-or-import) ps ys empty-trie
  where
  make-span : ctxt → 𝕃 tagged-val → err-m → span
  make-span Γ ts err = maybe-else
    (KndVar-span Γ orig (kvar-end-pos (fst orig) (snd orig) ys) ps checking ts err)
    (λ loc → Import-module-span Γ orig ps (loc :: ts) err)
    kind-or-import
  caap : 𝔹 → params → args → trie arg → spanM ⊤
  caap koi ((Decl _ pi _ x (Tkk k) _) :: ps) ((TypeArg T) :: ys) σ =
    get-ctxt λ Γ →
    check-type T (just (substs Γ σ k)) ≫span
    caap koi ps ys (trie-insert σ x $ TypeArg (qualif-type Γ T))
  caap ff ((Decl _ pi NotErased x (Tkt T) _) :: ps) ((TermArg NotErased t) :: ys) σ =
    get-ctxt λ Γ →
    let T' = substs Γ σ T in
    check-term t (just T') ≫span
    check-erased-margs t (just T') ≫span
    caap ff ps ys (trie-insert σ x $ TermArg NotErased (qualif-term Γ t))
  caap ff ((Decl _ pi Erased x (Tkt T) _) :: ps) ((TermArg NotErased t) :: ys) σ =
    get-ctxt λ Γ → 
    spanM-add (make-span Γ [ term-argument Γ t ]
                 (just ("A term argument was supplied for erased term parameter " ^ unqual-local x)))
  caap ff ((Decl _ pi NotErased x (Tkt T) _) :: ps) ((TermArg Erased t) :: ys) σ =
    get-ctxt λ Γ → 
    spanM-add (make-span Γ [ term-argument Γ t ]
                 (just ("An erased term argument was supplied for term parameter " ^ unqual-local x)))
  -- Either a kind argument or a correctly erased module argument
  caap koi ((Decl _ pi me x (Tkt T) _) :: ps) ((TermArg me' t) :: ys) σ =
    get-ctxt λ Γ →
    check-term t (just (substs Γ σ T)) ≫span
    caap koi ps ys (trie-insert σ x $ TermArg me (qualif-term Γ t))
  caap koi ((Decl _ x₁ _ x (Tkk x₃) x₄) :: ps₁) ((TermArg _ x₅) :: ys₂) σ =
    get-ctxt λ Γ → 
    spanM-add (make-span Γ [ term-argument Γ x₅ ]
                 (just ("A term argument was supplied for type parameter " ^ unqual-local x)))
  caap koi ((Decl _ x₁ _ x (Tkt x₃) x₄) :: ps₁) ((TypeArg x₅) :: ys₂) σ = 
    get-ctxt λ Γ → 
    spanM-add (make-span Γ [ type-argument Γ x₅ ]
                 (just ("A type argument was supplied for term parameter " ^ unqual-local x)))
  caap tt ((Decl _ _ _ x _ _) :: ps₁) [] σ =
    get-ctxt λ Γ → 
    spanM-add (make-span Γ []
                 (just ("Missing an argument for parameter " ^ unqual-local x)))
  caap ff ((Decl _ _ _ x _ _) :: ps₁) [] σ =
    get-ctxt λ Γ → spanM-add (make-span Γ [] nothing)
  caap koi [] (x₁ :: ys₂) σ = 
    get-ctxt λ Γ → 
    spanM-add (make-span Γ [ arg-argument Γ x₁ ]
                 (just "An extra argument was given"))
  caap koi [] [] σ =
    get-ctxt λ Γ → spanM-add (make-span Γ [] nothing)

check-erased-margs t mtp = get-ctxt λ Γ →
  let x = erased-margs Γ in
  if are-free-in skip-erased x t
  then spanM-add (erased-marg-span Γ t mtp)
  else spanMok

check-tk (Tkk k) = check-kind k
check-tk (Tkt t) = check-type t (just star)

check-def (DefTerm pi₁ x NoType t') =
  get-ctxt λ Γ → check-term t' nothing ≫=span cont (compileFail-in Γ t') t'
  where
  cont : 𝕃 tagged-val × err-m → term → maybe type → spanM (posinfo × var × restore-def × Σ tk λ atk → if tk-is-type atk then term else type)
  cont (tvs , err) t' (just T) =
    spanM-push-term-def pi₁ x t' T ≫=span λ m →
    get-ctxt λ Γ → 
    spanM-add (Var-span Γ pi₁ x synthesizing (type-data Γ T :: tvs) err) ≫span
    spanMr (pi₁ , x , m , Tkt T , t')
  cont (tvs , err) t' nothing = spanM-push-term-udef pi₁ x t' ≫=span λ m →
    get-ctxt λ Γ →
    spanM-add (Var-span Γ pi₁ x synthesizing tvs err) ≫span
    spanMr (pi₁ , x , m , Tkt (TpHole pi₁) , t')
check-def (DefTerm pi₁ x (SomeType T) t') =
  check-type T (just star) ≫span
  get-ctxt λ Γ →
  let T' = qualif-type Γ T in
  check-term t' (just T') ≫span 
  spanM-push-term-def pi₁ x t' T' ≫=span λ m →
  get-ctxt λ Γ →
  let p = compileFail-in Γ t' in
  spanM-add (Var-span Γ pi₁ x checking (type-data Γ T' :: fst p) (snd p)) ≫span
  spanMr (pi₁ , x , m , Tkt T , t')
check-def (DefType pi x k T) =
  check-kind k ≫span
  get-ctxt λ Γ →
  let k' = qualif-kind Γ k in
  check-type T (just k') ≫span
  spanM-push-type-def pi x T k' ≫=span λ m →
  get-ctxt λ Γ → spanM-add (Var-span Γ pi x checking ([ kind-data Γ k' ]) nothing) ≫span
  spanMr (pi , x , m , Tkk k , T)

check-case (Case pi x asₒ t) csₓ ctr-ps drop-ps Tₘ =
  spanM-add (pattern-span pi x asₒ) ≫span
  spanM-add (pattern-clause-span pi t) ≫span
  get-ctxt λ Γ →
  maybe-else' (trie-lookup (ctxt-get-qualif Γ) x ≫=maybe uncurry λ x' _ → trie-lookup csₓ x' ≫=maybe λ T → just (T ≫=maybe λ T → just (x' , T)))-- , decompose-ctr-type Γ T))
    (spanM-add (pattern-ctr-span Γ pi x asₒ nothing
      (just "This is not a constructor name")) ≫span spanMr (csₓ , [])) $
    maybe-else (spanM-add (pattern-ctr-span Γ pi x asₒ nothing (just "This case is unreachable")) ≫span spanMr (csₓ , []))
    (uncurry λ x' T → flip uncurry (decompose-ctr-type Γ T) λ Tₕ → uncurry λ ps is →
--      (x' , T , Tₕ , ps , is) →
        decl-args asₒ ps empty-trie [] ≫=spanc λ e → uncurry λ σ xs →
        let Tₘ' = TpAppt (apps-type Tₘ (ttys-to-args' Γ σ (drop drop-ps is))) (app-caseArgs (recompose-apps ctr-ps (mvar x')) asₒ) in
        spanM-add (pattern-ctr-span Γ pi x asₒ (just T) e) ≫span
        check-term t (just Tₘ') ≫span
        set-ctxt Γ ≫span
        spanMr (trie-insert csₓ x' nothing , reverse xs))
  where
  free-in-term : var → err-m
  free-in-term x = maybe-if (is-free-in skip-erased x t) ≫maybe just "Erased argument occurs free in the body of the term"
  ttys-to-args' = λ Γ σ → map λ {(tterm t) → TermArg NotErased (substs Γ σ t); (ttype T) → TypeArg (substs Γ σ T)}
  tpapp-caseArgs : type → caseArgs → type
  tpapp-caseArgs = foldl λ where
    (CaseTermArg pi me x) T → TpAppt T (mvar (pi % x))
    (CaseTypeArg pi x) T → TpApp T (mtpvar (pi % x))
  app-caseArgs : term → caseArgs → term
  app-caseArgs = foldl λ where
    (CaseTermArg pi me x) t → App t me (mvar (pi % x))
    (CaseTypeArg pi x) t → AppTp t (mtpvar (pi % x))
  --decl-args-xs : var → tk → caseArgs → var × tk × maybeErased × ℕ × ℕ
  --decl-args-xs x atk as = x , atk , λ n → let e = length asₒ + suc (suc n) in e ∸ length as , e
  range : posinfo × posinfo
  range = term-start-pos t , term-end-pos t
  decl-args : caseArgs → params → trie arg → 𝕃 (posinfo × var × tk × maybeErased × posinfo × posinfo) → spanM (err-m × trie arg × 𝕃 (posinfo × var × tk × maybeErased × posinfo × posinfo))
  decl-args ((CaseTermArg pi me x) :: as) ((Decl _ _ me' x' (Tkt T) _) :: ps) σ xs =
    get-ctxt λ Γ →
    let T' = substs Γ σ T
        e₁ = maybe-if (me xor me') ≫maybe just "Mismatched erasure of term argument"
        e₂ = maybe-if me ≫maybe free-in-term x in
    set-ctxt (ctxt-term-decl pi x T' Γ) ≫span get-ctxt λ Γ →
    spanM-add (Var-span Γ pi x checking ([ type-data Γ T' ]) (e₁ maybe-or e₂)) ≫span
    decl-args as ps (trie-insert σ x' (TermArg me (mvar (pi % x)))) ((pi , x , Tkt T' , me , range) :: xs)
  decl-args ((CaseTypeArg pi x) :: as) ((Decl _ _ _ x' (Tkk k) _) :: ps) σ xs =
    get-ctxt λ Γ →
    let k' = substs Γ σ k in
    set-ctxt (ctxt-type-decl pi x k' Γ) ≫span get-ctxt λ Γ →
    spanM-add (TpVar-span Γ pi x checking ([ kind-data Γ k' ]) (free-in-term x)) ≫span
    decl-args as ps (trie-insert σ x' (TypeArg (mtpvar (pi % x)))) ((pi , x , Tkk k' , Erased , range) :: xs)
  decl-args ((CaseTermArg pi me x) :: as) ((Decl _ _ me' x' (Tkk k) _) :: ps) σ xs =
    get-ctxt λ Γ →
    let k' = substs Γ σ k in
    set-ctxt (ctxt-var-decl-loc pi x Γ) ≫span get-ctxt λ Γ →
    spanM-add (Var-span Γ pi x checking [ expected-kind Γ k' ]
      (just "This term argument should be a type")) ≫span
    decl-args as ps (trie-insert σ x' (TermArg me $ mvar x)) ((pi , x , Tkk k' , me , range) :: xs)
  decl-args ((CaseTypeArg pi x) :: as) ((Decl _ _ me x' (Tkt T) _) :: ps) σ xs =
    get-ctxt λ Γ →
    let T' = substs Γ σ T in
    set-ctxt (ctxt-var-decl-loc pi x Γ) ≫span get-ctxt λ Γ →
    spanM-add (TpVar-span Γ pi x checking [ expected-type Γ T' ]
      (just ("This type argument should be a" ^ (if me then "n erased term" else " term")))) ≫span
    decl-args as ps (trie-insert σ x' (TypeArg $ mtpvar x)) ((pi , x , Tkt T' , Erased , range) :: xs)
  decl-args [] [] σ xs = spanMr (nothing , σ , xs)
  decl-args as [] σ xs = spanMr (just (ℕ-to-string (length as) ^ " too many arguments supplied") , σ , xs)
  decl-args [] ps σ xs = spanMr (just (ℕ-to-string (length ps) ^ " more arguments expected") , σ , xs)



check-cases cs csₓ ctr-ps drop-ps Tₘ = foldr -- {B = trie type → spanM (trie type × 𝕃 (var × tk × ℕ × ℕ))}
  (λ c x csₓ →
    check-case c csₓ ctr-ps drop-ps Tₘ ≫=spanc λ csₓ xs →
    x csₓ ≫=spanc λ csₓ xs' →
    spanMr (csₓ , (xs ++ xs')))
  (λ t → spanMr (t , [])) cs (trie-map just csₓ) ≫=spanc λ csₓ xs →
  get-ctxt λ Γ →
  let csₓ = trie-catMaybe csₓ in
  spanMr (maybe-if (trie-nonempty csₓ) ≫maybe
    just ("Missing pattern matching cases: " ^ 𝕃-to-string (unqual-all (ctxt-get-qualif Γ) ∘ fst) ", " (trie-mappings csₓ)) , xs)


check-mu-evidence NoTerm X as =
  get-ctxt λ Γ →
  spanMr $ maybe-else' (data-lookup Γ X as)
    (inj₁ $ "The head type of the subterm is not a datatype" , [ head-type Γ (mtpvar X) ])
    (inj₂ ∘' just ∘' _,_ id)
check-mu-evidence (SomeTerm t _) X as =
  get-ctxt λ Γ →
  check-term t nothing on-fail spanMr (inj₂ nothing) ≫=spanm' λ T →
  let ev-err = inj₁ $ ("The synthesized type of the evidence does not prove " ^ unqual-local (unqual-all (ctxt-get-qualif Γ) X) ^ " a datatype") ,
                      [ to-string-tag "evidence type" Γ T ] in
  case decompose-tpapps (hnf Γ (unfolding-elab unfold-head) T tt) of λ where
    (TpVar _ X' , as') → case reverse as' of λ where
      (ttype T :: as') → spanMr $ if ~ conv-type Γ T (mtpvar X) then ev-err else maybe-else ev-err (λ {d@(mk-data-info X x/mu asₚ asᵢ mps kᵢ k cs fcs) → (inj₂ ∘' just ∘' _,_ (mapp $ recompose-apps (asₚ ++ ttys-to-args Erased asᵢ) $ mvar $ data-to/ X)) d}) (data-lookup-mu Γ X' $ reverse as' ++ as) -- TODO: Make sure "X" isn't a _defined_ type, but a _declared_ one! This way we avoid the possibility that "as" has arguments to parameters in it, but only to indices.
      _ → spanMr ev-err
    _ → spanMr ev-err

check-refinement : type → kind → spanM (𝕃 tagged-val × err-m)
check-refinement T k Γ ss =
  check-type T (just k) (qualified-ctxt Γ) (regular-spans nothing []) ≫=monad λ where
    (triv , _ , ss') → returnM $ (λ x → x , Γ , ss) $
      [ to-string-tag "computed motive" Γ T ] ,
      if (spans-have-error ss')
        then just "We could not compute a well-kinded motive"
        else nothing

check-mu pi pi' x? t ot Tₘ? pi'' cs pi''' mtp =
  get-ctxt λ Γ → 
  check-termi t nothing ≫=span λ T →
  let ret-tp = λ ps as t → case Tₘ? of λ {
        (SomeType Tₘ) → just $ hnf Γ (unfolding-elab unfold-head) (TpAppt (apps-type (qualif-type Γ Tₘ) $
                          ttys-to-args NotErased (drop (length ps) as)) t) tt;
        NoType → mtp}
      Tₘ?' = optType-elim Tₘ? nothing just in
  case_of_ (maybe-map (λ T → decompose-tpapps $ hnf Γ (unfolding-elab unfold-head) T tt) T) λ where
    (just (TpVar _ X , as)) →
      check-mu-evidence ot X as on-fail
       (uncurry λ e tvs → spanM-add (Mu-span Γ pi x? pi''' Tₘ?' (maybe-to-checking mtp)
         (expected-type-if Γ mtp ++ tvs) $ just e) ≫span
        return-when mtp (ret-tp [] as $ qualif-term Γ t))
       ≫=spans' λ where
        nothing →
          spanM-add (Mu-span Γ pi x? pi''' Tₘ?' (maybe-to-checking mtp)
            (expected-type-if Γ mtp ++ [ head-type Γ (mtpvar X) ]) nothing) ≫span
          return-when mtp (ret-tp [] as $ qualif-term Γ t)
        (just (cast , mk-data-info Xₒ x/mu asₚ asᵢ ps kᵢ k cs' fcs)) →
          let is = kind-to-indices Γ kᵢ
              no-motive = spanMr (nothing , [] ,
                            just "A motive is required when synthesizing") in
          (case Tₘ? of λ where
            (SomeType Tₘ) →
              check-type Tₘ (just kᵢ) ≫span spanMr (just (qualif-type Γ Tₘ) , [] , nothing)
            NoType →
              spanMr mtp on-fail no-motive ≫=spanm' λ Tₑ →
              let Tₘ = refine-motive Γ is (asᵢ ++ [ tterm (qualif-term Γ t) ]) Tₑ in
              check-refinement Tₘ kᵢ ≫=span λ p2 → spanMr (just Tₘ , p2))
          ≫=spanc λ Tₘ → uncurry λ tvs₁ e₁ → spanMr Tₘ ≫=spanr λ Tₘ →
          let is = drop-last 1 is
              subst-ctr : ctxt → ctr → ctr
              subst-ctr = λ {Γ (Ctr pi x T) →
                Ctr pi x $ flip (hnf Γ $ unfolding-elab unfold-head) ff $ maybe-else' x?
                  (if (Xₒ =string X) then T else subst Γ (params-to-tplams ps $ mtpvar X) Xₒ T)
                  λ x → subst Γ (params-to-tplams ps $ mtpvar $ pi' % mu-Type/ x) Xₒ T}
              reduce-cs = map λ {(Ctr pi x T) → Ctr pi x $ hnf Γ (unfolding-elab unfold-head) T ff}
              cs' = reduce-cs $ maybe-else' x? (if Xₒ =string X then cs' else fcs X) λ x → fcs (mu-Type/ (pi' % x))
              Γ' = maybe-else' x? (spanMr (Γ , [])) λ x →
                     let X' = mu-Type/ x
                         xₘᵤ = mu-isType/ x
                         qXₒₘᵤ = data-Is/ Xₒ
                         qXₜₒ = data-to/ Xₒ
                         qX' = pi' % X'
                         qxₘᵤ = pi' % xₘᵤ
                         Tₘᵤ = TpApp (flip apps-type asₚ $ mtpvar qXₒₘᵤ) $ mtpvar qX'
                         Γ' = ctxt-term-def pi' localScope OpacTrans xₘᵤ nothing Tₘᵤ $
                              ctxt-datatype-decl Xₒ (pi' % x) asₚ $
                              ctxt-type-decl-no-qualif pi' X' k Γ
                         freshₓ = fresh-var (add-indices-to-ctxt is Γ') (maybe-else "x" id (is-var (tterm t)))
                         Tₓ = hnf Γ' (unfolding-elab unfold-head) (indices-to-alls is $ Abs posinfo-gen Pi posinfo-gen freshₓ (Tkt $ indices-to-tpapps is $ mtpvar qX') $ TpAppt (indices-to-tpapps is Tₘ) $ mapp (indices-to-apps is $ mappe (AppTp (flip apps-term asₚ $ mvar qXₜₒ) $ mtpvar qX') $ mvar $ qxₘᵤ) $ mvar freshₓ) ff
                         Γ'' = ctxt-term-decl-no-qualif pi' x Tₓ Γ'
                         e₂? = x/mu ≫maybe just "Abstract datatypes can only be pattern matched by μ'"
                         e₃ = λ x → just $ x ^ " occurs free in the erasure of the body (not allowed)"
                         e₃ₑ = flip (are-free-in-cases skip-erased) cs ∘ stringset-insert* empty-stringset
                         e₃ₓ? = λ x → maybe-if (e₃ₑ [ x ]) ≫maybe e₃ x
                         e₃? = x? ≫=maybe λ x → maybe-if (e₃ₑ $ mu-isType/ x :: mu-Type/ x :: []) ≫=maybe λ _ →
                                 e₃ₓ? (mu-isType/ x) maybe-or e₃ₓ? (mu-Type/ x)in
                     spanM-add (var-span NotErased Γ'' pi' x checking (Tkt Tₓ) (e₂? maybe-or e₃?)) ≫span
                     spanMr (Γ'' ,
                             (binder-data Γ'' pi' X' (Tkk k) Erased nothing pi'' pi''' ::
                              binder-data Γ'' pi' x (Tkt Tₓ) NotErased nothing pi'' pi''' ::
                              binder-data Γ'' pi' xₘᵤ (Tkt Tₘᵤ) Erased nothing pi'' pi''' ::
                              to-string-tag X' Γ'' k ::
                              to-string-tag xₘᵤ Γ'' Tₘᵤ ::
                              to-string-tag x Γ'' Tₓ ::
                              [])) in
          Γ' ≫=spanc λ Γ' bds → with-ctxt Γ'
            (let cs'' = foldl (λ {(Ctr pi x T) σ → trie-insert σ x T}) empty-trie cs'
                 drop-ps = maybe-else 0 length (maybe-not x? ≫maybe (maybe-if (Xₒ =string X) ≫maybe just ps))
                 scrutinee = cast $ qualif-term Γ t
                 Tᵣ = ret-tp ps (args-to-ttys asₚ ++ asᵢ) scrutinee in
             check-cases cs cs'' asₚ drop-ps Tₘ ≫=spanc λ e₂ xs →
             spanM-add (elim-pair (maybe-else' Tᵣ ([] , just "A motive is required when synthesizing")
                                    (check-for-type-mismatch-if Γ "synthesized" mtp))
               λ tvs e₃ → Mu-span Γ pi x? pi''' Tₘ?' (maybe-to-checking mtp)
                 (map (λ {(pi , x , atk , me , s , e) →
                            binder-data Γ' pi x atk me nothing s e}) xs ++ tvs₁ ++ tvs ++ bds) (e₁ maybe-or (e₂ maybe-or e₃))) ≫span
             return-when mtp Tᵣ)
    (just (Tₕ , as)) →
      spanM-add (Mu-span Γ pi x? pi''' Tₘ?' (maybe-to-checking mtp)
        [ head-type Γ Tₕ ] (just "The head type of the subterm is not a datatype")) ≫span
      return-when mtp (ret-tp [] as (qualif-term Γ t))
    nothing → check-fail mtp

