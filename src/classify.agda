import cedille-options
open import general-util
module classify (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib

open import cedille-types
open import constants
open import conversion
open import ctxt
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

check-erasure-binder-match : maybeErased → binder → 𝔹
check-erasure-binder-match Erased All = tt
check-erasure-binder-match NotErased Pi = tt
check-erasure-binder-match _ _ = ff

check-erasure-arrow-match : maybeErased → arrowtype → 𝔹
check-erasure-arrow-match Erased ErasedArrow = tt
check-erasure-arrow-match NotErased UnerasedArrow = tt
check-erasure-arrow-match m t = ff

check-erasures-match : (m₁ m₂ : maybeErased) → 𝔹
check-erasures-match Erased Erased = tt
check-erasures-match NotErased NotErased = tt
check-erasures-match m₁ m₂ = ff

hnf-from : ctxt → (e : 𝔹) → maybeMinus → term → term
hnf-from Γ e EpsHnf t = hnf Γ (unfolding-set-erased unfold-head e) t tt
hnf-from Γ e EpsHanf t = hanf Γ e t

-- TODO Should these be unerased sometimes?
check-term-update-eq : ctxt → leftRight → maybeMinus → posinfo → term → term → posinfo → type
check-term-update-eq Γ Left m pi t1 t2 pi' = TpEq pi (hnf-from Γ tt m t1) t2 pi'
check-term-update-eq Γ Right m pi t1 t2 pi' = TpEq pi t1 (hnf-from Γ tt m t2)  pi'
check-term-update-eq Γ Both m pi t1 t2 pi' = TpEq pi (hnf-from Γ tt m t1) (hnf-from Γ tt m t2) pi'

-- a simple incomplete check for beta-inequivalence
{-
{-# TERMINATING #-}
check-beta-inequivh : stringset → stringset → renamectxt → term → term → 𝔹
check-beta-inequivh local-left local-right m (Lam _ _ _ x1 _ t1) (Lam _ _ _ x2 _ t2) = 
  check-beta-inequivh (stringset-insert local-left x1) (stringset-insert local-right x2) (renamectxt-insert m x1 x2) t1 t2
check-beta-inequivh local-left local-right m (Lam _ _ _ x1 _ t1) t2 = 
  check-beta-inequivh (stringset-insert local-left x1) (stringset-insert local-right x1) m t1 (mapp t2 (mvar x1))
check-beta-inequivh local-left local-right m t1 (Lam _ _ _ x2 _ t2) = 
  check-beta-inequivh (stringset-insert local-left x2) (stringset-insert local-right x2) m (mapp t1 (mvar x2)) t2
check-beta-inequivh local-left local-right m t1 t2 with decompose-apps t1 | decompose-apps t2 
check-beta-inequivh local-left local-right m t1 t2 | Var _ x1 , args1 | Var _ x2 , args2 = 
  (~ eq-var m x1 x2) && (stringset-contains local-left x1) && (stringset-contains local-right x2)
check-beta-inequivh local-left local-right m t1 t2 | _ | _ = ff 

-- t1 and t2 should be in normal form
check-beta-inequiv : term → term → 𝔹
check-beta-inequiv t1 t2 = check-beta-inequivh empty-trie empty-trie empty-renamectxt t1 t2
-}

add-tk' : erased? → defScope → posinfo → var → tk → spanM restore-def
add-tk' e s pi x atk = 
   helper atk ≫=span λ mi → 
    (if ~ (x =string ignored-var) then
       (get-ctxt λ Γ → 
          spanM-add (var-span e Γ pi x checking atk nothing))
    else spanMok) ≫span
   spanMr mi
  where helper : tk → spanM restore-def
        helper (Tkk k) = spanM-push-type-decl pi s x k 
        helper (Tkt t) = spanM-push-term-decl pi s x t

add-mod-tk : posinfo → var → tk → spanM restore-def
add-mod-tk = add-tk' ff globalScope

add-tk : posinfo → var → tk → spanM restore-def
add-tk = add-tk' ff localScope
    
check-type-return : ctxt → kind → spanM (maybe kind)
check-type-return Γ k = spanMr (just (hnf Γ unfold-head k tt))

check-termi-return : ctxt → (subject : term) → type → spanM (maybe type)
check-termi-return Γ subject tp = spanMr (just (hnf Γ (unfolding-elab unfold-head) tp tt))

lambda-bound-var-conv-error : ctxt → var → tk → tk → 𝕃 tagged-val → 𝕃 tagged-val × string
lambda-bound-var-conv-error Γ x atk atk' tvs = 
  (("the variable" , [[ x ]] , []) :: (to-string-tag-tk "its declared classifier" Γ atk') :: [ to-string-tag-tk "the expected classifier" Γ atk ]) ++ tvs ,
  "The classifier given for a λ-bound variable is not the one we expected"

lambda-bound-class-if : optClass → tk → tk
lambda-bound-class-if NoClass atk = atk
lambda-bound-class-if (SomeClass atk') atk = atk'
{-
var-spans-term : term → spanM ⊤
var-spans-optTerm : optTerm → spanM ⊤
var-spans-term (App t x t') = spanM-add (App-span t t' checking [] nothing) ≫span var-spans-term t ≫span var-spans-term t'
var-spans-term (AppTp t x) = var-spans-term t 
var-spans-term (Beta x ot ot') = var-spans-optTerm ot ≫span var-spans-optTerm ot' 
var-spans-term (Chi x x₁ t) = var-spans-term t
var-spans-term (Epsilon x x₁ x₂ t) = var-spans-term t
var-spans-term (Hole x) = spanM-add (hole-span empty-ctxt x nothing [])
var-spans-term (Let pi (DefTerm pi' x m t) t') =
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl pi' x Γ in
      set-ctxt Γ' ≫span
      spanM-add (Let-span Γ checking pi (DefTerm pi' x m t) t' [] nothing) ≫span
      spanM-add (Var-span Γ' pi' x untyped [] nothing) ≫span
      var-spans-term t ≫span
      var-spans-term t' ≫span      
      set-ctxt Γ)
var-spans-term (Let pi (DefType pi' x k t) t') = 
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl pi' x Γ in
      set-ctxt Γ' ≫span
      spanM-add (Var-span Γ' pi' x untyped [] nothing) ≫span
      var-spans-term t' ≫span      
      set-ctxt Γ)
var-spans-term (Lam pi l pi' x _ t) =
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl pi' x Γ in
      set-ctxt Γ' ≫span
      spanM-add (Lam-span Γ checking pi l x NoClass t [] nothing) ≫span
      spanM-add (Var-span Γ' pi' x untyped [] nothing) ≫span
      var-spans-term t ≫span
      set-ctxt Γ)
var-spans-term (Parens x t x₁) = var-spans-term t
var-spans-term (Phi pi eq t₁ t₂ pi') = var-spans-term eq ≫span var-spans-term t₁ ≫span var-spans-term t₂
var-spans-term (Rho _ _ _ t _ t') = var-spans-term t ≫span var-spans-term t'
var-spans-term (Sigma x t) = var-spans-term t
var-spans-term (Theta x x₁ t x₂) = var-spans-term t
var-spans-term (Var pi x) =
  get-ctxt (λ Γ →
    spanM-add (Var-span Γ pi x untyped [] (if ctxt-binds-var Γ x then nothing
                                        else just "This variable is not currently in scope." )))
var-spans-term (IotaPair _ t1 t2 _ _) = var-spans-term t1 ≫span var-spans-term t2
var-spans-term (IotaProj t _ _) = var-spans-term t

var-spans-optTerm NoTerm = spanMok
var-spans-optTerm (SomeTerm t _) = var-spans-term t
-}

{- for check-term and check-type, if the optional classifier is given, we will check against it.
   Otherwise, we will try to synthesize a type.  

   check-termi does not have to worry about normalizing the type it is given or the one it
   produces, nor about instantiating with the subject.  This will be handled by interleaved 
   calls to check-term.

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
{-# TERMINATING #-}
check-term : term → (m : maybe type) → spanM (check-ret m)
check-termi : term → (m : maybe type) → spanM (check-ret m)
check-term-app : term → (m : maybe type) → spanM (maybe (meta-vars × type))
check-type : type → (m : maybe kind) → spanM (check-ret m)
check-typei : type → (m : maybe kind) → spanM (check-ret m)
check-kind : kind → spanM ⊤
check-args-against-params : (kind-or-import : 𝔹) → (posinfo × var) → params → args → spanM ⊤
check-tk : tk → spanM ⊤
check-meta-vars : meta-vars → spanM (maybe error-span) -- no way to know when checking failed!

check-term tm nothing =
    check-termi tm nothing
  ≫=span λ where
    nothing → spanMr nothing
    (just tp) →
      get-ctxt λ Γ → spanMr (just (hnf Γ (unfolding-elab unfold-head) tp tt))
check-term tm (just tp)
  =   get-ctxt λ Γ → check-termi tm (just (hnf Γ (unfolding-elab unf) tp tt))
  where
  unf = if is-intro-form tm then unfold-head-rec-defs else unfold-head

check-type subject nothing = check-typei subject nothing
check-type subject (just k)
  = get-ctxt (λ Γ → check-typei subject (just (hnf Γ (unfolding-elab unfold-head) k tt)))

check-termi (Parens pi t pi') tp =
  spanM-add (punctuation-span "Parens" pi pi') ≫span
  check-termi t tp
check-termi (Var pi x) mtp =
  get-ctxt (cont mtp)
  where cont : (mtp : maybe type) → ctxt → spanM (check-ret mtp)
        cont mtp Γ with ctxt-lookup-term-var Γ x
        cont mtp Γ | nothing = 
         spanM-add (Var-span Γ pi x (maybe-to-checking mtp)
                      (expected-type-if Γ mtp ++ [ missing-type ]) (just "Missing a type for a term variable.")) ≫span
         return-when mtp mtp
        cont nothing Γ | just tp = 
          spanM-add (Var-span Γ pi x synthesizing (type-data Γ tp :: [ hnf-type Γ tp ]) nothing) ≫span
          check-termi-return Γ (Var pi x) tp
        cont (just tp) Γ | just tp' = 
          spanM-add (uncurry (Var-span Γ pi x checking) (check-for-type-mismatch Γ "synthesized" tp tp'))

check-termi t'@(AppTp t tp') tp
  =   check-term-app t' tp
    ≫=span λ ret → case ret of λ where
      nothing → check-fail tp
      -- TODO ensure meta-vars is solved!
      (just (Xs , tp')) →
        get-ctxt λ Γ →
        return-when tp (just (meta-vars-subst-type Γ Xs tp'))

-- =BUG= =ACG= =31= Maybe pull out repeated code in helper functions?
check-termi t''@(App t m t') tp
  =   check-term-app t'' tp
    ≫=span λ ret → case ret of λ where
      nothing → check-fail tp
      -- TODO ensure meta-vars is solved!
      (just (Xs , tp')) →
        get-ctxt λ Γ →
        return-when tp (just (meta-vars-subst-type Γ Xs tp'))

check-termi (Let pi d t) mtp =
  -- spanM-add (punctuation-span "Let" pi (posinfo-plus pi 3)) ≫span
  add-def d ≫=span finish
  where finish : (var × restore-def) → spanM (check-ret mtp)
        finish (x , m) = 
         get-ctxt (λ Γ → 
         spanM-add (Let-span Γ (maybe-to-checking mtp) pi d t [] nothing) ≫span
         check-term t mtp ≫=span λ r →
         spanM-restore-info x m ≫span
         spanMr r)

        noterased = "keywords" , [[ "noterased" ]] , []

        add-def : defTermOrType → spanM (var × restore-def)
        add-def (DefTerm pi₁ x NoCheckType t') =
           get-ctxt λ Γ → check-term t' nothing ≫=span cont (compileFail-in Γ t') t'
          where cont : 𝕃 tagged-val × err-m → term → maybe type → spanM (var × restore-def)
                cont (tvs , err) t' (just T) = spanM-push-term-def pi₁ nonParamVar x t' T ≫=span λ m →
                                     get-ctxt λ Γ → 
                                       spanM-add (Var-span Γ pi₁ x synthesizing (type-data Γ T :: noterased :: tvs) err) ≫span
                                     spanMr (x , m)
                cont (tvs , err) t' nothing = spanM-push-term-udef pi₁ x t' ≫=span λ m →
                                    get-ctxt λ Γ →
                                      spanM-add (Var-span Γ pi₁ x synthesizing (noterased :: tvs) err) ≫span
                                    spanMr (x , m)
        add-def (DefTerm pi₁ x (Type T) t') =
          check-type T (just star) ≫span
          get-ctxt λ Γ →
          let T' = qualif-type Γ T in
          check-term t' (just T') ≫span 
          spanM-push-term-def pi₁ nonParamVar x t' T' ≫=span λ m →
          get-ctxt λ Γ →
            let p = compileFail-in Γ t' in
            spanM-add (Var-span Γ pi₁ x checking (type-data Γ T' :: noterased :: fst p) (snd p)) ≫span
          spanMr (x , m)
        add-def (DefType pi x k T) =
          check-kind k ≫span
          get-ctxt λ Γ →
          let k' = qualif-kind Γ k in
          check-type T (just k') ≫span
          spanM-push-type-def pi nonParamVar x T k' ≫=span λ m →
          get-ctxt λ Γ → spanM-add (Var-span Γ pi x checking (noterased :: [ kind-data Γ k' ]) nothing) ≫span
          spanMr (x , m)

check-termi (Lam pi l pi' x (SomeClass atk) t) nothing =
  spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
    add-tk pi' x atk ≫=span λ mi → 
    check-term t nothing ≫=span (λ mtp → 
    spanM-restore-info x mi ≫span -- now restore the context
    cont mtp)

  where cont : maybe type → spanM (maybe type)
        cont nothing =
          get-ctxt (λ Γ → 
           spanM-add (Lam-span Γ synthesizing pi l x (SomeClass atk) t [] nothing) ≫span 
                       spanMr nothing)
        cont (just tp) =
          get-ctxt (λ Γ → 
           let atk' = qualif-tk Γ atk in
           -- This should indeed "unqualify" occurrences of x in tp for rettp
           let rettp = abs-tk l x pi' atk' (rename-type Γ (pi' % x) x (tk-is-type atk) tp) in
           let tvs = [ type-data Γ rettp ] in
           let p = if lam-is-erased l && is-free-in skip-erased x t then just "The bound variable occurs free in the erasure of the body (not allowed)." , [ erasure Γ t ] else nothing , [] in
           spanM-add (Lam-span Γ synthesizing pi l x (SomeClass atk') t 
                       (snd p ++ tvs) (fst p)) ≫span
           check-termi-return Γ (Lam pi l pi' x (SomeClass atk) t) rettp)

check-termi (Lam pi l _ x NoClass t) nothing =
  get-ctxt (λ Γ → 
    spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
    spanM-add (Lam-span Γ synthesizing pi l x NoClass t []
                (just ("We are not checking this abstraction against a type, so a classifier must be"
                            ^ " given for the bound variable " ^ x))) ≫span
    spanMr nothing)

check-termi (Lam pi l pi' x oc t) (just tp) with to-abs tp 
check-termi (Lam pi l pi' x oc t) (just tp) | just (mk-abs pi'' b pi''' x' atk _ tp') =
  check-oc oc ≫span
  spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
  get-ctxt (λ Γ → 
    spanM-add (uncurry (this-span Γ atk oc) (check-erasures Γ l b)) ≫span
    (add-tk' (lam-is-erased l) localScope pi' x (lambda-bound-class-if oc atk)) ≫=span λ mi → 
    get-ctxt (λ Γ' → check-term t (just (rename-type Γ x' (qualif-var Γ' x) (tk-is-type atk) tp'))) ≫span
    spanM-restore-info x mi) 
  where this-span : ctxt → tk → optClass → 𝕃 tagged-val → err-m → span
        this-span Γ _ NoClass tvs = Lam-span Γ checking pi l x oc t tvs
        this-span Γ atk (SomeClass atk') tvs err = 
          if conv-tk Γ (qualif-tk Γ atk') atk then
            Lam-span Γ checking pi l x oc t tvs err
          else
            let p = lambda-bound-var-conv-error Γ x atk atk' tvs in
            Lam-span Γ checking pi l x oc t (fst p) (just (snd p))
        check-oc : optClass → spanM ⊤
        check-oc NoClass = spanMok
        check-oc (SomeClass atk) = check-tk atk
        check-erasures : ctxt → lam → binder → 𝕃 tagged-val × err-m
        check-erasures Γ ErasedLambda All = 
          if is-free-in skip-erased x t
            then type-data Γ tp :: [ erasure Γ t ] , just "The Λ-bound variable occurs free in the erasure of the body."
            else [ type-data Γ tp ] , nothing
        check-erasures Γ KeptLambda Pi = [ type-data Γ tp ] , nothing
        check-erasures Γ ErasedLambda Pi =  [ expected-type Γ tp ] , just ("The expected type is a Π-abstraction (indicating explicit input), but"
                                              ^ " the term is a Λ-abstraction (implicit input).")
        check-erasures Γ KeptLambda All =  [ expected-type Γ tp ] , just ("The expected type is a ∀-abstraction (indicating implicit input), but"
                                              ^ " the term is a λ-abstraction (explicit input).")
check-termi (Lam pi l pi' x oc t) (just tp) | nothing =
   get-ctxt (λ Γ →
    spanM-add (punctuation-span "Lambda"  pi (posinfo-plus pi 1)) ≫span
    spanM-add (Lam-span Γ checking pi l x oc t [ expected-type Γ tp ] (just "The expected type is not of the form that can classify a λ-abstraction")))


check-termi (Beta pi ot ot') (just (TpEq pi' t1 t2 pi'')) = 
  untyped-optTerm-spans ot ≫span
  untyped-optTerm-spans ot' ≫span
  get-ctxt (λ Γ → 
    if conv-term Γ t1 t2 then
      spanM-add (Beta-span pi (optTerm-end-pos-beta pi ot ot')
                   checking [ type-data Γ (TpEq pi' t1 t2 pi'') ] (optTerm-conv Γ ot))
    else
      spanM-add (Beta-span pi (optTerm-end-pos-beta pi ot ot')
                  checking [ expected-type Γ (TpEq pi' t1 t2 pi'') ] (just "The two terms in the equation are not β-equal")))
  where
    optTerm-conv : ctxt → optTerm → err-m
    optTerm-conv Γ NoTerm = nothing
    optTerm-conv Γ (SomeTerm t _) = if conv-term Γ (qualif-term Γ t) t1 then nothing else just "The expected type does not match the synthesized type"

check-termi (Beta pi ot ot') (just tp) = 
  get-ctxt (λ Γ → 
   untyped-optTerm-spans ot ≫span
   untyped-optTerm-spans ot' ≫span
   spanM-add (Beta-span pi (optTerm-end-pos-beta pi ot ot') checking [ expected-type Γ tp ] (just "The expected type is not an equation.")))

check-termi (Beta pi (SomeTerm t pi') ot) nothing =
  get-ctxt λ Γ →
   untyped-term-spans t ≫span
   untyped-optTerm-spans ot ≫span
   let tp = qualif-type Γ (TpEq posinfo-gen t t posinfo-gen) in
   spanM-add (Beta-span pi (optTerm-end-pos-beta pi (SomeTerm t pi') ot) synthesizing [ type-data Γ tp ] nothing) ≫span
   spanMr (just tp)

check-termi (Beta pi ot ot') nothing = 
  untyped-optTerm-spans ot ≫span
  untyped-optTerm-spans ot' ≫span
  spanM-add (Beta-span pi (optTerm-end-pos-beta pi ot ot') synthesizing [] (just "An expected type is required in order to type a use of plain β.")) ≫span
  spanMr nothing

check-termi (Epsilon pi lr m t) (just (TpEq pi' t1 t2 pi'')) = 
  get-ctxt (λ Γ → 
  spanM-add (Epsilon-span pi lr m t checking [ type-data Γ (TpEq pi' t1 t2 pi'') ] nothing) ≫span
    check-term t (just (check-term-update-eq Γ lr m pi' t1 t2 pi'')))

check-termi (Epsilon pi lr m t) (just tp) = 
  get-ctxt (λ Γ → 
  spanM-add (Epsilon-span pi lr m t checking [ expected-type Γ tp ] (just "The expected type is not an equation, when checking an ε-term.")))
check-termi (Epsilon pi lr m t) nothing = 
  check-term t nothing ≫=span cont
  where cont : maybe type → spanM (maybe type)
        cont nothing = 
          spanM-add (Epsilon-span pi lr m t synthesizing [] (just ("There is no expected type, and we could not synthesize a type from the body"
                                                           ^ " of the ε-term."))) ≫span
          spanMr nothing
        cont (just (TpEq pi' t1 t2 pi'')) =
          get-ctxt (λ Γ → 
            let r = check-term-update-eq Γ lr m pi' t1 t2 pi'' in
            spanM-add (Epsilon-span pi lr m t synthesizing [ type-data Γ r ] nothing) ≫span
            spanMr (just r))
        cont (just tp) = 
          get-ctxt (λ Γ → 
          spanM-add (Epsilon-span pi lr m t synthesizing [ to-string-tag "the synthesized type" Γ tp ]
                                                          (just ("There is no expected type, and the type we synthesized for the body"
                                                            ^ " of the ε-term is not an equation."))) ≫span
          spanMr nothing)

check-termi (Sigma pi t) mt = 
  check-term t nothing ≫=span cont mt
  where cont : (outer : maybe type) → maybe type → spanM (check-ret outer)
        cont mt nothing = 
          get-ctxt (λ Γ → 
          spanM-add (Sigma-span Γ pi t mt [] (just ("We could not synthesize a type from the body"
                                                    ^ " of the ς-term."))) ≫span
          check-fail mt)
        cont mt (just (TpEq pi' t1 t2 pi'')) with TpEq pi' t2 t1 pi'' 
        cont nothing (just (TpEq pi' t1 t2 pi'')) | r =
          get-ctxt (λ Γ → 
          spanM-add (Sigma-span Γ pi t nothing [ type-data Γ r ] nothing) ≫span
          spanMr (just r))
        cont (just tp) (just (TpEq pi' t1 t2 pi'')) | r =
          get-ctxt (λ Γ → 
            spanM-add (uncurry (Sigma-span Γ pi t (just tp)) (check-for-type-mismatch Γ "synthesized" tp r)))
        cont mt (just tp) = 
          get-ctxt (λ Γ → 
          spanM-add (Sigma-span Γ pi t mt [ to-string-tag "the synthesized type" Γ tp ] (just ("The type we synthesized for the body"
                                                      ^ " of the ς-term is not an equation."))) ≫span
          check-fail mt)

check-termi (Phi pi t₁≃t₂ t₁ t₂ pi') (just tp) =
  get-ctxt (λ Γ →
    check-term t₁≃t₂ (just (qualif-type Γ (TpEq posinfo-gen t₁ t₂ posinfo-gen)))) ≫span
  check-term t₁ (just tp) ≫span
  untyped-term-spans t₂ ≫span
  get-ctxt (λ Γ → spanM-add (Phi-span pi pi' checking [ type-data Γ tp ] nothing))

check-termi (Phi pi t₁≃t₂ t₁ t₂ pi') nothing =
  get-ctxt (λ Γ →
    check-term t₁≃t₂ (just (qualif-type Γ (TpEq posinfo-gen t₁ t₂ posinfo-gen)))) ≫span
  check-term t₁ nothing ≫=span λ mtp →
  untyped-term-spans t₂ ≫span
  get-ctxt (λ Γ → spanM-add
    (Phi-span pi pi' synthesizing (type-data-tvs Γ mtp) nothing)) ≫span
  spanMr mtp
    where
      type-data-tvs : ctxt → maybe type → 𝕃 tagged-val
      type-data-tvs Γ (just tp) = type-data Γ tp :: [ hnf-type Γ tp ]
      type-data-tvs Γ nothing = []


check-termi (Rho pi op on t (Guide pi' x tp) t') nothing =
  get-ctxt λ Γ →
  spanM-add (Var-span (ctxt-var-decl pi' x Γ) pi' x synthesizing [] nothing) ≫span
  check-term t' nothing ≫=span λ mtp →
  untyped-optGuide-spans (Guide pi' x tp) ≫span
  check-term t nothing ≫=span λ where
    (just (TpEq _ t1 t2 _)) → maybe-else
      (spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) [] nothing) ≫span spanMr nothing)
      (λ tp' →
        let tp'' = qualif-type Γ (subst-type Γ t1 x tp) in
        let tp''' = qualif-type Γ (subst-type Γ t2 x tp) in
        if conv-type Γ tp'' tp'
          then (spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) [ type-data Γ tp''' ] nothing) ≫span spanMr (just tp'''))
          else (spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) (type-data Γ tp' :: [ expected-type-subterm Γ tp'' ])
            (just "The expected type of the subterm does not match the synthesized type")) ≫span spanMr nothing)) mtp
    (just _) → spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) []
                 (just "We could not synthesize an equation from the first subterm in a ρ-term.")) ≫span spanMr nothing
    nothing → spanM-add (Rho-span pi t t' synthesizing op (inj₂ x) [] nothing) ≫span check-term t' nothing

check-termi (Rho pi op on t (Guide pi' x tp) t') (just tp') =
  get-ctxt λ Γ →
  untyped-optGuide-spans (Guide pi' x tp) ≫span
  check-term t nothing ≫=span λ where
    (just (TpEq _ t1 t2 _)) →
      let tp'' = qualif-type Γ (subst-type Γ t2 x tp) in -- This is t2 (and t1 below) so that Cedille Core files are correctly checked by regular Cedille
      let tp''' = qualif-type Γ (subst-type Γ t1 x tp) in
      let err = if conv-type Γ tp'' tp' then nothing else just "The expected type does not match the specified type" in
      spanM-add (Rho-span pi t t' checking op (inj₂ x) (type-data Γ tp'' :: [ expected-type Γ tp' ]) err) ≫span
      spanM-add (Var-span (ctxt-var-decl pi' x Γ) pi' x checking [] nothing) ≫span
      check-term t' (just tp''')
    (just _) → spanM-add (Rho-span pi t t' checking op (inj₂ x) []
                 (just "We could not synthesize an equation from the first subterm in a ρ-term."))
    nothing → spanM-add (Rho-span pi t t' checking op (inj₂ x) [] nothing) ≫span check-term t' (just tp)

check-termi (Rho pi op on t NoGuide t') (just tp) = 
  check-term t nothing ≫=span cont
  where cont : maybe type → spanM ⊤
        cont nothing = get-ctxt (λ Γ → spanM-add (Rho-span pi t t' checking op (inj₁ 0) [ expected-type Γ tp ] nothing) ≫span check-term t' (just tp))
        cont (just (TpEq pi' t1 t2 pi'')) = 
           get-ctxt (λ Γ →
             let ns-err = optNums-to-stringset on in
             let s = rewrite-type tp Γ empty-renamectxt (is-rho-plus op) (fst ns-err) t1 t2 0 in
             check-term t' (just (fst s)) ≫span
             get-ctxt (λ Γ →
             spanM-add (Rho-span pi t t' checking op (inj₁ (fst (snd s))) ((to-string-tag "the equation" Γ (TpEq pi' t1 t2 pi'')) :: [ type-data Γ tp ]) (snd ns-err (snd (snd s))))))
        cont (just tp') =
          get-ctxt (λ Γ → spanM-add (Rho-span pi t t' checking op (inj₁ 0)
                                     ((to-string-tag "the synthesized type for the first subterm" Γ tp')
                                       :: [ expected-type Γ tp ])
                                     (just "We could not synthesize an equation from the first subterm in a ρ-term.")))

check-termi (Rho pi op on t NoGuide t') nothing = 
  check-term t nothing ≫=span λ mtp → 
  check-term t' nothing ≫=span cont mtp
  where cont : maybe type → maybe type → spanM (maybe type)
        cont (just (TpEq pi' t1 t2 pi'')) (just tp) = 
          get-ctxt (λ Γ → 
            let ns-err = optNums-to-stringset on in
            let s = rewrite-type tp Γ empty-renamectxt (is-rho-plus op) (fst ns-err) t1 t2 0 in
            let tp' = fst s in
              spanM-add (Rho-span pi t t' synthesizing op (inj₁ (fst (snd s))) [ type-data Γ tp' ] (snd ns-err (snd (snd s)))) ≫span
              check-termi-return Γ (Rho pi op on t NoGuide t') tp')
        cont (just tp') m2 =
           get-ctxt (λ Γ → spanM-add (Rho-span pi t t' synthesizing op (inj₁ 0) [ to-string-tag "the synthesized type for the first subterm" Γ tp' ]
                                         (just "We could not synthesize an equation from the first subterm in a ρ-term.")) ≫span spanMr nothing)
        cont nothing _ = spanM-add (Rho-span pi t t' synthesizing op (inj₁ 0) [] nothing) ≫span spanMr nothing

check-termi (Chi pi (Atype tp) t) mtp =
  check-type tp (just star) ≫span
  get-ctxt λ Γ →
  let tp' = qualif-type Γ tp in
  check-termi t (just tp') ≫span cont tp' mtp
  where cont : type → (m : maybe type) → spanM (check-ret m)
        cont tp' nothing = get-ctxt (λ Γ → spanM-add (Chi-span Γ pi (Atype tp) t synthesizing [] nothing) ≫span spanMr (just tp'))
        cont tp' (just tp'') =
          get-ctxt (λ Γ → 
           spanM-add (uncurry (Chi-span Γ pi (Atype tp') t checking) (check-for-type-mismatch Γ "asserted" tp'' tp')))
check-termi (Chi pi NoAtype t) (just tp) = 
  check-term t nothing ≫=span cont 
  where cont : (m : maybe type) → spanM ⊤
        cont nothing = get-ctxt (λ Γ → spanM-add (Chi-span Γ pi NoAtype t checking [] nothing) ≫span spanMok)
        cont (just tp') =
          get-ctxt (λ Γ → 
            spanM-add (uncurry (Chi-span Γ pi NoAtype t checking) (check-for-type-mismatch Γ "synthesized" tp tp')))
check-termi (Chi pi NoAtype t) nothing =
 get-ctxt λ Γ → spanM-add (Chi-span Γ pi NoAtype t synthesizing [] nothing) ≫span check-term t nothing

check-termi (Delta pi mT t) mtp =
  check-term t (just delta-contra) ≫span
  get-ctxt λ Γ →
  spanM-add (Delta-span Γ pi mT t (maybe-to-checking mtp) [] nothing) ≫span
  (case mT of λ where
    NoAtype → spanMr compileFailType
    (Atype T) → check-type T (just (Star posinfo-gen)) ≫span spanMr T) ≫=span λ T → 
  return-when mtp (just (qualif-type Γ T))

check-termi (Theta pi u t ls) nothing =
  get-ctxt (λ Γ →
  spanM-add (Theta-span Γ pi u t ls synthesizing []
               (just "Theta-terms can only be used in checking positions (and this is a synthesizing one)."))
  ≫span spanMr nothing)

check-termi (Theta pi AbstractEq t ls) (just tp) =
  -- discard spans from checking t, because we will check it again below
  check-term t nothing ≫=spand cont
  where cont : maybe type → spanM ⊤
        cont nothing = check-term t nothing ≫=span λ m → 
                       get-ctxt λ Γ →
                          spanM-add (Theta-span Γ pi AbstractEq t ls checking [ expected-type Γ tp ] (just "We could not compute a motive from the given term"))
                                      -- (expected-type Γ tp :: [ motive-label , [[ "We could not compute a motive from the given term" ]] , [] ]))))
        cont (just htp) =
           get-ctxt (λ Γ → 
             let x = (fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt) in
             let motive = mtplam x (Tkt htp) (TpArrow (TpEq posinfo-gen t (mvar x) posinfo-gen) UnerasedArrow tp) in
               spanM-add (Theta-span Γ pi AbstractEq t ls checking (expected-type Γ tp :: [ the-motive Γ motive ]) nothing) ≫span 
               check-term (App* (AppTp t (NoSpans motive (posinfo-plus (term-end-pos t) 1)))
                              (lterms-to-𝕃 AbstractEq ls))
                 (just tp))

check-termi (Theta pi Abstract t ls) (just tp) =
  -- discard spans from checking the head, because we will check it again below
  check-term t nothing ≫=spand cont t
  where cont : term → maybe type → spanM ⊤
        cont _ nothing = check-term t nothing ≫=span λ m → 
                         get-ctxt λ Γ →
                           spanM-add (Theta-span Γ pi Abstract t ls checking [ expected-type Γ tp ] (just "We could not compute a motive from the given term"))
                                      -- (expected-type Γ tp :: [ motive-label , [[ "We could not compute a motive from the given term" ]] , [] ]))))
        cont t (just htp) = 
          let x = compute-var t in
          let motive = mtplam x (Tkt htp) tp in
           get-ctxt (λ Γ →
            spanM-add (Theta-span Γ pi Abstract t ls checking (expected-type Γ tp :: [ the-motive Γ motive ]) nothing) ≫span 
            check-term (App* (AppTp t (NoSpans motive (term-end-pos t)))
                            (lterms-to-𝕃 Abstract ls)) 
               (just tp))
          where compute-var : term → string
                compute-var (Var pi' x) = x
                compute-var t = ignored-var

check-termi (Theta pi (AbstractVars vs) t ls) (just tp) =
  get-ctxt (λ Γ → cont (wrap-vars Γ vs (substs-type empty-ctxt (rep-vars Γ vs empty-trie) tp)))
  where wrap-var : ctxt → var → type → maybe type
        wrap-var Γ v tp = ctxt-lookup-tk-var Γ v ≫=maybe (λ atk → just (mtplam v atk tp))
        wrap-vars : ctxt → vars → type → maybe type
        wrap-vars Γ (VarsStart v) tp = wrap-var Γ v tp
        wrap-vars Γ (VarsNext v vs) tp = wrap-vars Γ vs tp ≫=maybe (λ tp → wrap-var Γ v tp)
        cont : maybe type → spanM ⊤
        cont nothing = check-term t nothing ≫=span (λ m → 
                       get-ctxt (λ Γ →
                          spanM-add (Theta-span Γ pi (AbstractVars vs) t ls checking
                                      [ expected-type Γ tp ] (just ("We could not compute a motive from the given term"
                                                                       ^ " because one of the abstracted vars is not in scope.")))))
        cont (just motive) =
           get-ctxt (λ Γ →
            spanM-add (Theta-span Γ pi (AbstractVars vs) t ls checking (expected-type Γ tp :: [ the-motive Γ motive ]) nothing) ≫span 
            check-term (App* (AppTp t (NoSpans motive (posinfo-plus (term-end-pos t) 1)))
                            (lterms-to-𝕃 Abstract ls))
               (just tp))
        rep-var : ctxt → var → trie term → trie term
        rep-var Γ v ρ with trie-lookup (ctxt-get-qualif Γ) v
        ...| nothing = ρ
        ...| just (v' , _) = trie-insert ρ v' (Var posinfo-gen v)
        rep-vars : ctxt → vars → trie term → trie term
        rep-vars Γ (VarsStart v) = rep-var Γ v
        rep-vars Γ (VarsNext v vs) ρ = rep-vars Γ vs (rep-var Γ v ρ)

check-termi (Hole pi) tp =
  get-ctxt (λ Γ → spanM-add (hole-span Γ pi tp []) ≫span return-when tp tp)

check-termi (IotaPair pi t1 t2 og pi') (just (Iota pi1 pi2 x tp1 tp2)) =
  check-term t1 (just tp1) ≫span
  get-ctxt (λ Γ → 
    let t1' = qualif-term Γ t1 in
    let t2' = qualif-term Γ t2 in
    check-term t2 (just (subst-type Γ t1' x tp2)) ≫span
    optGuide-spans og checking ≫span
    check-optGuide og ≫=span λ e →
    -- TODO why another get-ctxt here?
    get-ctxt (λ Γ →
    let cc = check-conv Γ t1' t2' e in
    spanM-add (IotaPair-span pi pi' checking (expected-type Γ (Iota pi1 pi2 x tp1 tp2) :: snd cc) (fst cc))))
  where ntag : ctxt → string → string → term → unfolding → tagged-val
        ntag Γ nkind which t u = to-string-tag (nkind ^ " of the " ^ which ^ " component: ") Γ (hnf Γ u t tt)
        err : ctxt → string → term → tagged-val
        err Γ which t = ntag Γ "Hnf" which t unfold-head
        check-conv : ctxt → term → term → err-m → err-m × 𝕃 tagged-val
        check-conv Γ t1 t2 e = if conv-term Γ t1 t2
          then e , []
          else just "The two components of the iota-pair are not convertible (as required)." ,
                       err Γ "first" t1 :: [ err Γ "second" t2 ]
        check-optGuide : optGuide → spanM err-m
        check-optGuide NoGuide = spanMr nothing
        check-optGuide (Guide pi x' tp) = get-ctxt λ Γ → with-ctxt (ctxt-term-decl pi localScope x' tp1 Γ) (check-type tp (just (Star posinfo-gen))) ≫span
          spanMr (if conv-type Γ tp2 (qualif-type (ctxt-var-decl pi2 x Γ) (subst-type Γ (Var pi2 x) x' tp))
            then nothing
            else just "The expected type does not match the guided type")

check-termi (IotaPair pi t1 t2 (Guide pi' x T2) pi'') nothing =
  get-ctxt λ Γ →
  check-term t1 nothing ≫=span λ T1 →
  check-term t2 (just (qualif-type Γ (subst-type Γ (qualif-term Γ t1) x T2))) ≫span
  maybe-else spanMok (λ T1 → with-ctxt (ctxt-term-decl pi' localScope x T1 Γ) (check-type T2 (just (Star posinfo-gen)))) T1 ≫span
  let T2' = qualif-type (ctxt-var-decl pi' x Γ) T2 in
  spanM-add (IotaPair-span pi pi'' synthesizing (maybe-else [] (λ T1 → [ type-data Γ (Iota posinfo-gen posinfo-gen x T1 T2') ]) T1) nothing) ≫span
  spanM-add (Var-span (ctxt-var-decl pi' x Γ) pi' x synthesizing [] nothing) ≫span
  spanMr (T1 ≫=maybe λ T1 → just (Iota posinfo-gen posinfo-gen x T1 T2'))
  where
    err : ctxt → err-m × 𝕃 tagged-val
    err Γ = if conv-term Γ t1 t2
      then nothing , []
      else just "The two components of the iota-pair are not convertible (as required)." ,
        to-string-tag "Hnf of the first component" Γ (hnf Γ unfold-head t1 tt) ::
        [ to-string-tag "Hnf of the second component" Γ (hnf Γ unfold-head t2 tt) ]

check-termi (IotaPair pi t1 t2 og pi') (just tp) =
  get-ctxt (λ Γ →
  spanM-add (IotaPair-span pi pi' checking [ expected-type Γ tp ] (just "The type we are checking against is not a iota-type")))

check-termi (IotaPair pi t1 t2 NoGuide pi') nothing =
  spanM-add (IotaPair-span pi pi' synthesizing [] (just "Iota pairs require a specified type when in a synthesizing position")) ≫span
  spanMr nothing


check-termi (IotaProj t n pi) mtp =
  check-term t nothing ≫=span cont' mtp (posinfo-to-ℕ n)
  where cont : (outer : maybe type) → ℕ → (computed : type) → spanM (check-ret outer)
        cont mtp n computed with computed
        cont mtp 1 computed | Iota pi' pi'' x t1 t2 =
          get-ctxt (λ Γ →
            spanM-add (uncurry (λ tvs → IotaProj-span t pi (maybe-to-checking mtp) (head-type Γ computed :: tvs))
                                           (check-for-type-mismatch-if Γ "synthesized" mtp t1)) ≫span
            return-when mtp (just t1))
        cont mtp 2 computed | Iota pi' pi'' x a t2 =
          get-ctxt (λ Γ →
            let t2' = subst-type Γ (qualif-term Γ t) x t2 in
              spanM-add (uncurry (λ tvs → IotaProj-span t pi (maybe-to-checking mtp)
                          (head-type Γ computed :: tvs)) (check-for-type-mismatch-if Γ "synthesized" mtp t2')) ≫span
              return-when mtp (just t2'))
        cont mtp n computed | Iota pi' pi'' x t1 t2 =
          get-ctxt (λ Γ →
          spanM-add (IotaProj-span t pi (maybe-to-checking mtp) [ head-type Γ computed ] (just "Iota-projections must use .1 or .2 only.")) ≫span return-when mtp mtp)
        cont mtp n computed | _ =
          get-ctxt (λ Γ →
          spanM-add (IotaProj-span t pi (maybe-to-checking mtp) [ head-type Γ computed ] (just "The head type is not a iota-abstraction.")) ≫span return-when mtp mtp)
        cont' : (outer : maybe type) → ℕ → (computed : maybe type) → spanM (check-ret outer)
        cont' mtp _ nothing = spanM-add (IotaProj-span t pi (maybe-to-checking mtp) [] nothing) ≫span return-when mtp mtp
        cont' mtp n (just tp) = get-ctxt (λ Γ → cont mtp n (hnf Γ unfold-head-rec-defs tp tt))
                                                     -- we are looking for iotas in the bodies of rec defs

{-check-termi t tp = get-ctxt (λ Γ → spanM-add (unimplemented-term-span Γ (term-start-pos t) (term-end-pos t) tp) ≫span unimplemented-if tp)-}

-- check-term-app
----------------------------------------
check-term-app-return : ctxt → (subject : term)
                        → meta-vars → type → spanM (maybe (meta-vars × type))
check-term-app-return Γ subject Xs tp
  = spanMr (just (Xs , hnf Γ unfold-head tp tt))

-- errors
check-term-app-error-inapp : ctxt → (t t' : term) → type → meta-vars
                             → checking-mode → maybeErased → spanM ⊤
check-term-app-error-inapp Γ t t' htp Xs m e
  = spanM-add
      (App-span t t' m (term-app-head Γ t :: head-type Γ (meta-vars-subst-type Γ Xs htp)
        :: [ term-argument Γ t' ])
        (just ("The type computed for the head of the application does"
          ^ " not allow the head to be applied to " ^ h e ^ " argument ")))
  where h : maybeErased → string
        h Erased = "an erased term"
        h NotErased = "a term"

check-term-app-error-unmatchable : ∀ {A} ctxt → (ht t : term) (htpₓ tp : type)
                                   → meta-vars → checking-mode → string → spanM (maybe A)
check-term-app-error-unmatchable Γ tₓ t tpₓ tp Xs cm msg
  =   spanM-add (App-span tₓ t cm (arg-exp-type Γ tpₓ :: arg-type Γ tp :: meta-vars-data Γ Xs) (just msg))
    ≫span spanMr nothing

check-term-app-error-erased : ∀ {A} checking-mode → maybeErased
                              → (t t' : term) → type → meta-vars → spanM (maybe A)
check-term-app-error-erased c m t t' htp Xs
  =   get-ctxt λ Γ → spanM-add
        (App-span t t' c
          (term-app-head Γ t :: [ head-type Γ (meta-vars-subst-type Γ Xs htp )]) (just (msg m)))
    ≫span spanMr nothing
  where msg : maybeErased → string
        msg Erased = ("The type computed for the head requires"
                    ^ " an explicit (non-erased) argument, but the application"
                    ^ " is marked as erased")
        msg NotErased = ("The type computed for the head requires"
                    ^ " an implicit (erased) argument, but the application"
                    ^ " is marked as not erased")

check-term-app-meta-var-app-span : (Xs Xs-solved : meta-vars) (Γ : ctxt) (res-tp : type) (chk-tp : maybe type) → maybe error-span → 𝕃 tagged-val × err-m
check-term-app-meta-var-app-span Xs Xs-solved Γ res-tp chk-tp (just (mk-error-span nm pi pi' tvs err))
  = (meta-vars-data Γ Xs-solved ++ tvs) , just err
check-term-app-meta-var-app-span Xs Xs-solved Γ res-tp chk-tp nothing
  = fst p ++ meta-vars-data Γ Xs-solved , snd p

  where p = meta-vars-check-type-mismatch-if chk-tp Γ "synthesized" Xs res-tp

-- main definition
check-term-app t''@(App t m t') mtp
  -- check head
  =   check-term-app t nothing
    on-fail (spanM-add (App-span t t' check-mode [] nothing)
            ≫span spanMr nothing)
    ≫=spanm' λ { (Xs , htp) →
      check-app-agree m htp Xs
    ≫=spanr λ {ret@(Xs , tp') →
      spanMr (just ret)}}
  where
  -- TODO include meta-vars in errors
  check-mode = maybe-to-checking mtp

  check-app-agree : maybeErased → type → meta-vars
                    → spanM (maybe (meta-vars × type))
  check-app-agree m tp Xs
    = get-ctxt λ Γ →
      case meta-vars-unfold-tmapp Γ Xs tp of λ where
        (Xs , yes-tp-arrow tp tpₐ m' cod) →
          if ~ check-erasures-match m m'
            then check-term-app-error-erased check-mode m t t' tp Xs
          else if ~ meta-vars-are-free-in-type Xs tpₐ
            then   check-term t' (just tpₐ)
                 ≫span spanM-add
                   (uncurry (App-span t t' check-mode)
                     ((meta-vars-check-type-mismatch-if mtp Γ "synthesized" Xs (cod t'))))
                 ≫span check-term-app-return Γ t'' Xs (cod t')
          else   check-term t' nothing
               on-fail   spanM-add (App-span t t' check-mode
                           ([ head-type Γ (meta-vars-subst-type Γ Xs tp)]) nothing)
                      ≫span spanMr nothing
               ≫=spanm' λ tpₐ' → case meta-vars-match Γ Xs empty-trie tpₐ tpₐ' of λ where
                 (yes-error msg) →
                   check-term-app-error-unmatchable Γ t t' tpₐ tpₐ' Xs check-mode msg
                 (no-error   Xs) →
                     -- All meta-vars solved in the last match
                     spanMr (meta-vars-in-type Xs tpₐ)
                   ≫=span λ Xsₐ → check-meta-vars Xsₐ
                   ≫=span λ me →
                     spanM-add
                       (uncurry (λ tvs → App-span t t' check-mode
                                  (arg-exp-type Γ tpₐ :: arg-type Γ tpₐ' :: tvs))
                         (check-term-app-meta-var-app-span Xs Xsₐ
                           Γ (cod t') mtp me))
                   ≫span check-term-app-return Γ t'' (meta-vars-update-kinds Γ Xs Xsₐ) (cod t')
        (Xs , no-tp-arrow tp) →
            check-term-app-error-inapp Γ t t' tp Xs check-mode m
          ≫span spanMr nothing 

check-term-app (AppTp t tp) mtp
  -- check head
  =   check-term-app t nothing
        on-fail spanM-add ((AppTp-span t tp check-mode []  nothing))
          ≫span spanMr nothing
    ≫=spanm' λ {(Xs , htp) → get-ctxt λ Γ →
      -- check agreement (trying the unsolved head type first)
      check-term-app-agree (hnf Γ unfold-head-rec-defs htp tt) tp Xs
        on-fail (check-term-app-to-tp-error Γ Xs htp)
    ≫=spanm' λ {ret@(Xs , tp') → get-ctxt λ Γ →
      spanM-add (uncurry (AppTp-span t tp check-mode)
        (meta-vars-check-type-mismatch-if mtp Γ "synthesized" Xs
          (hnf Γ unfold-head tp' tt)))
    ≫span spanMr (just ret)}}
    where
    check-mode = maybe-to-checking mtp

    check-term-app-agree : (htp tp : type) → meta-vars
                           → spanM (maybe (meta-vars × type))
    check-term-app-agree htp tp Xs
      = get-ctxt λ Γ →
        case (meta-vars-unfold-tpapp Γ Xs htp) of λ where
          (no-tp-abs _) → spanMr nothing
          (yes-tp-abs pi b pi' x k htp') →
              -- TODO avoid double substitution
              check-type tp (just (meta-vars-subst-kind Γ Xs k))
            ≫span get-ctxt λ Γ →
              let X    = meta-vars-fresh-tp Xs x k (just (qualif-type Γ tp))
                  htp″ = subst-type Γ (TpVar pi' (meta-var-name X)) x htp'
                  Xs'  = meta-vars-add Xs X
              in spanMr (just (meta-vars-add Xs X , htp″))

    -- TODO bring into check-term-app-error-inapp
    check-term-app-to-tp-error : ctxt → meta-vars → type → spanM _
    check-term-app-to-tp-error Γ Xs htp = get-ctxt
      λ Γ → spanM-add (AppTp-span t tp synthesizing
              (term-app-head Γ t
                :: head-type Γ (meta-vars-subst-type Γ Xs htp)
                :: [ type-argument Γ tp ])
              (just ("The type computed for the head of the application does"
                   ^ " not allow the head to be applied to the (type) argument ")))
      ≫span spanMr nothing

check-term-app t m
  = check-term t nothing  -- synthesize type for head
    ≫=spanm' λ htp → spanMr (just (meta-vars-empty , htp))
----------------------------------------
----------------------------------------


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
check-typei (TpLambda pi pi' x atk body) (just k) | just (mk-absk pik pik' x' atk' _ k') =
   check-tk atk ≫span
   spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
   get-ctxt (λ Γ → 
   spanM-add (if conv-tk Γ (qualif-tk Γ atk) atk' then
                TpLambda-span pi x atk body checking [ kind-data Γ k ] nothing
              else
                uncurry (λ tvs err → TpLambda-span pi x atk body checking tvs (just err)) (lambda-bound-var-conv-error Γ x atk' atk [ kind-data Γ k ])) ≫span
   add-tk pi' x atk ≫=span λ mi → 
   get-ctxt (λ Γ' → check-type body (just (rename-kind Γ x' (qualif-var Γ' x) (tk-is-type atk') k'))) ≫span
   spanM-restore-info x mi)
check-typei (TpLambda pi pi' x atk body) (just k) | nothing = 
   check-tk atk ≫span
   spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
   get-ctxt (λ Γ →
   spanM-add (TpLambda-span pi x atk body checking [ expected-kind Γ k ]
               (just "The type is being checked against a kind which is not an arrow- or Pi-kind.")))

check-typei (TpLambda pi pi' x atk body) nothing =
  spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  check-type body nothing ≫=span
  cont ≫=span (λ mk →
  spanM-restore-info x mi ≫span
  spanMr mk)

  where cont : maybe kind → spanM (maybe kind)
        cont nothing = 
          spanM-add (TpLambda-span pi x atk body synthesizing [] nothing) ≫span
          spanMr nothing
        cont (just k) =
             get-ctxt (λ Γ →
              let atk' = qualif-tk Γ atk in
              -- This should indeed "unqualify" occurrences of x in k for r
              let r = absk-tk x pi' atk' (rename-kind Γ (pi' % x) x (tk-is-type atk) k) in
              spanM-add (TpLambda-span pi x atk' body synthesizing [ kind-data Γ r ] nothing) ≫span
              spanMr (just r))

check-typei (Abs pi b {- All or Pi -} pi' x atk body) k = 
  get-ctxt (λ Γ →
  spanM-add (uncurry (TpQuant-span (binder-is-pi b) pi x atk body (maybe-to-checking k))
               (if-check-against-star-data Γ "A type-level quantification" k)) ≫span
  spanM-add (punctuation-span "Forall" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  check-type body (just star) ≫span
  spanM-restore-info x mi ≫span
  return-star-when k)

check-typei (TpArrow t1 _ t2) k = 
  get-ctxt (λ Γ →
  spanM-add (uncurry (TpArrow-span t1 t2 (maybe-to-checking k)) (if-check-against-star-data Γ "An arrow type" k)) ≫span
  check-type t1 (just star) ≫span
  check-type t2 (just star) ≫span
    return-star-when k)

check-typei (TpAppt tp t) k =
  check-type tp nothing ≫=span cont'' ≫=spanr cont' k
  where cont : kind → spanM (maybe kind)
        cont (KndTpArrow tp' k') = 
          check-term t (just tp') ≫span 
          spanMr (just k')
        cont (KndPi _ _ x (Tkt tp') k') = 
          check-term t (just tp') ≫span 
          get-ctxt (λ Γ → 
            spanMr (just (subst-kind Γ (qualif-term Γ t) x k')))
        cont k' = get-ctxt (λ Γ → 
                   spanM-add (TpAppt-span tp t (maybe-to-checking k)
                               (type-app-head Γ tp
                                 :: head-kind Γ k' 
                                 :: [ term-argument Γ t ])
                               (just ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a term"))) ≫span
                  spanMr nothing)
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          get-ctxt (λ Γ →
          spanM-add (TpAppt-span tp t synthesizing [ kind-data Γ k ] nothing) ≫span
            check-type-return Γ k)
        cont' (just k') k = 
          get-ctxt (λ Γ → 
            if conv-kind Γ k k' then spanM-add (TpAppt-span tp t checking (expected-kind Γ k' :: [ kind-data Γ k ]) nothing)
            else spanM-add (TpAppt-span tp t checking (expected-kind Γ k' :: [ kind-data Γ k ])
              (just "The kind computed for a type application does not match the expected kind.")))
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
          get-ctxt (λ Γ → 
            spanMr (just (subst-kind Γ (qualif-type Γ tp') x k')))
        cont k' = get-ctxt (λ Γ → 
                  spanM-add (TpApp-span tp tp' (maybe-to-checking k)
                               (type-app-head Γ tp
                                 :: head-kind Γ k' 
                                 :: [ type-argument Γ tp' ])
                               (just ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a type"))) ≫span
                  spanMr nothing)
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          get-ctxt (λ Γ → 
          spanM-add (TpApp-span tp tp' synthesizing [ kind-data Γ k ] nothing) ≫span
            check-type-return Γ k)
        cont' (just k') k = 
          get-ctxt (λ Γ → 
            if conv-kind Γ k k' then spanM-add (TpApp-span tp tp' checking (expected-kind Γ k' :: [ kind-data Γ k' ]) nothing)
            else spanM-add (TpApp-span tp tp' checking (expected-kind Γ k' :: [ kind-data Γ k ])
                           (just "The kind computed for a type application does not match the expected kind.")))
        cont'' : maybe kind → spanM (maybe kind)
        cont'' nothing = spanM-add (TpApp-span tp tp' (maybe-to-checking k) [] nothing) ≫span spanMr nothing
        cont'' (just k) = cont k

check-typei (TpEq pi t1 t2 pi') k = 
  get-ctxt (λ Γ → 
    untyped-term-spans t1 ≫span
    set-ctxt Γ ≫span 
    untyped-term-spans t2 ≫span
    set-ctxt Γ) ≫span 
    get-ctxt (λ Γ → 
    spanM-add (uncurry (TpEq-span pi t1 t2 pi' (maybe-to-checking k)) (if-check-against-star-data Γ "An equation" k)) ≫span
    spanM-add (unchecked-term-span t1) ≫span
    spanM-add (unchecked-term-span t2) ≫span
    return-star-when k)

check-typei (Lft pi pi' X t l) k = 
  add-tk pi' X (Tkk star) ≫=span λ mi → 
  get-ctxt λ Γ → check-term t (just (qualif-type Γ (liftingType-to-type X l))) ≫span
  spanM-add (punctuation-span "Lift" pi (posinfo-plus pi 1)) ≫span
  spanM-restore-info X mi ≫span
  cont k (qualif-kind Γ (liftingType-to-kind l))
  where cont : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont nothing k = get-ctxt (λ Γ → spanM-add (Lft-span pi X t synthesizing [ kind-data Γ k ] nothing) ≫span spanMr (just k))
        cont (just k') k = 
          get-ctxt (λ Γ → 
            if conv-kind Γ k k' then 
              spanM-add (Lft-span pi X t checking ( expected-kind Γ k' :: [ kind-data Γ k ]) nothing)
            else
              spanM-add (Lft-span pi X t checking ( expected-kind Γ k' :: [ kind-data Γ k ]) (just "The expected kind does not match the computed kind.")))
check-typei (Iota pi pi' x t1 t2) mk =
  get-ctxt (λ Γ → 
  spanM-add (uncurry (Iota-span pi t2 (maybe-to-checking mk)) (if-check-against-star-data Γ "A iota-type" mk)) ≫span
  check-typei t1 (just star) ≫span
  add-tk pi' x (Tkt t1) ≫=span λ mi → 
  check-typei t2 (just star) ≫span
  spanM-restore-info x mi ≫span
  return-star-when mk)

{-check-typei (Iota pi pi' x NoType t2) mk =
  get-ctxt (λ Γ → 
  spanM-add (uncurry (λ tvs err → Iota-span pi t2 tvs
    (if isJust err then err else just "Iota-abstractions in source text require a type for the bound variable."))
  (if-check-against-star-data Γ "A iota-type" mk)) ≫span
  return-star-when mk)-}

check-kind (KndParens pi k pi') =
  spanM-add (punctuation-span "Parens (kind)" pi pi') ≫span
  check-kind k
check-kind (Star pi) = spanM-add (Star-span pi checking nothing)

check-kind (KndVar pi x ys) =
  get-ctxt λ Γ → helper (ctxt-lookup-kind-var-qdef Γ x)
  where helper : maybe (params × kind) → spanM ⊤
        helper (just (ps , k)) = check-args-against-params tt (pi , x) ps ys
        helper nothing = get-ctxt λ Γ →
          spanM-add (KndVar-span Γ (pi , x) (kvar-end-pos pi x ys) ParamsNil checking []
            (just "Undefined kind variable"))

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
  spanM-add (KndPi-span pi x atk k checking nothing) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  check-kind k ≫span
  spanM-restore-info x mi

check-args-against-params kind-or-import orig ps ys =
  caap ps ys ≫=span λ m →
  spanM-restore-info* m
  where
  str = if kind-or-import then "kind" else "import"
  make-span : ctxt → 𝕃 tagged-val → err-m → span
  make-span Γ = if kind-or-import
    then KndVar-span Γ orig (kvar-end-pos (fst orig) (snd orig) ys) ps checking
    else Import-module-span Γ orig ps
  caap : params → args → spanM (𝕃 (string × restore-def))
  caap (ParamsCons (Decl _ pi x (Tkk k) _) ps) (ArgsCons (TypeArg T) ys) =
    check-type T (just k) ≫span
    spanM-push-type-def pi paramVar x T k ≫=span λ m → 
    caap ps ys ≫=span λ ms →
    spanMr ((x , m) :: ms)
  caap (ParamsCons (Decl _ pi x (Tkt T) _) ps) (ArgsCons (TermArg t) ys) =
    check-term t (just T) ≫span
    spanM-push-term-def pi paramVar x t T ≫=span λ m → 
    caap ps ys ≫=span λ ms →
    spanMr ((x , m) :: ms)
  caap (ParamsCons (Decl _ x₁ x (Tkk x₃) x₄) ps₁) (ArgsCons (TermArg x₅) ys₂) =
    get-ctxt (λ Γ → 
    spanM-add (make-span Γ [ term-argument Γ x₅ ]
                 ( just ("A term argument was supplied for type parameter " ^ x ^ " of the defined " ^ str ^ ".")))) ≫span
    spanMr []
  caap (ParamsCons (Decl _ x₁ x (Tkt x₃) x₄) ps₁) (ArgsCons (TypeArg x₅) ys₂) = 
    get-ctxt (λ Γ → 
    spanM-add (make-span Γ [ type-argument Γ x₅ ]
                 ( just ("A type argument was supplied for type parameter " ^ x ^ " of the defined " ^ str ^ ".")))) ≫span
    spanMr []
  caap (ParamsCons (Decl _ _ x _ _) ps₁) ArgsNil =
    get-ctxt (λ Γ → 
    spanM-add (make-span Γ []
                 (just ("Missing an argument for parameter " ^ x ^ " of the defined  " ^ str ^ ".")))) ≫span
    spanMr []             
  caap ParamsNil (ArgsCons x₁ ys₂) = 
    get-ctxt (λ Γ → 
    spanM-add (make-span Γ [ arg-argument Γ x₁ ]
                 (just ("An extra argument was given to the defined  " ^ str ^ ".")))) ≫span
    spanMr []                                             
  caap ParamsNil ArgsNil =
    get-ctxt (λ Γ → spanM-add (make-span Γ [] nothing)) ≫span spanMr []


check-tk (Tkk k) = check-kind k
check-tk (Tkt t) = check-type t (just star)

check-meta-vars Xs -- pi
  =   (with-qualified-qualif $' with-clear-error
        (  get-ctxt λ Γ → sequence-spanM
             (for (varset-ordered Γ) yield λ where
               (meta-var-mk x (meta-var-tm tp mtm)) → spanMok
               (meta-var-mk-tp x k nothing) → spanMok
               (meta-var-mk-tp x k (just tp)) →
                   get-error λ es → if (isJust es) then spanMok else
                   check-type tp (just k)
                 ≫span (spanM-push-type-def posinfo-gen nonParamVar x tp k
                 ≫=span λ _ → spanMok))
         ≫=span λ _ → get-error λ es → spanMr es))
    ≫=spand λ es → spanMr (maybe-map retag es)

  where
  open helpers
  varset-ordered : ctxt → 𝕃 meta-var
  varset-ordered Γ = drop-nothing $' for (meta-vars.order Xs) yield λ where
    x → (trie-lookup (meta-vars.varset (meta-vars-update-kinds Γ Xs Xs)) x)


  -- replace qualif info with one where the keys are the fully qualified variable names
  qualified-qualif : qualif → qualif
  qualified-qualif q = for trie-mappings q accum empty-trie do λ where
    (_ , qi@(v , as)) q → trie-insert q v qi

  -- helper to restore qualif state
  with-qualified-qualif : ∀ {A} → spanM A → spanM A
  with-qualified-qualif sm
    =   get-ctxt λ Γ →
      with-ctxt (ctxt-set-qualif Γ (qualified-qualif (ctxt-get-qualif Γ)))
        sm

  -- helper to restore error state
  with-clear-error : ∀ {A} → spanM A → spanM A
  with-clear-error m
    =   get-error λ es → set-error nothing
      ≫span m
      ≫=span λ a → set-error es
      ≫span spanMr a

  retag : error-span → error-span
  retag (mk-error-span dsc pi pi' tvs err)
    = let tvs' = for tvs yield λ where
                   (t , v) → "meta-var " ^ t , v
      in mk-error-span dsc pi pi' tvs' err
    where open helpers
