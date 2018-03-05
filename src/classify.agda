import cedille-options
module classify (options : cedille-options.options) where

open import lib
open import general-util

open import cedille-types
open import constants
open import conversion
open import ctxt
open import is-free
open import lift
open import rename
open import rewriting
open import meta-vars options
open import spans options
open import subst
open import syntax-util
open import to-string options

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

if-check-against-star-data : ctxt → string → maybe kind → 𝕃 tagged-val
if-check-against-star-data Γ desc nothing = [ kind-data Γ star ]
if-check-against-star-data Γ desc (just (Star _)) = [ kind-data Γ star ]
if-check-against-star-data Γ desc (just k) = error-data (desc ^ " is being checked against a kind other than ★")
                                        :: expected-kind Γ k
                                        :: []

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

hnf-from : ctxt → maybeMinus → term → term
hnf-from Γ EpsHnf t = hnf Γ unfold-head t tt
hnf-from Γ EpsHanf t = hanf Γ t

check-term-update-eq : ctxt → leftRight → maybeMinus → term → term → type
check-term-update-eq Γ Left m t1 t2 = TpEq (hnf-from Γ m t1) t2
check-term-update-eq Γ Right m t1 t2 = TpEq t1 (hnf-from Γ m t2) 
check-term-update-eq Γ Both m t1 t2 = TpEq (hnf-from Γ m t1) (hnf-from Γ m t2) 

-- a simple incomplete check for beta-inequivalence
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

add-tk' : erased? → defScope → posinfo → var → tk → spanM restore-def
add-tk' e s pi x atk = if (x =string ignored-var) then spanMr (nothing , nothing) else
       (helper atk ≫=span λ mi → 
        (get-ctxt λ Γ → 
          spanM-add (var-span e Γ pi x checking atk)) ≫span
        spanMr mi)
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
check-termi-return Γ subject tp = spanMr (just (hnf Γ unfold-head tp tt))

lambda-bound-var-conv-error : ctxt → var → tk → tk → 𝕃 tagged-val → 𝕃 tagged-val
lambda-bound-var-conv-error Γ x atk atk' tvs = 
    ( error-data "The classifier given for a λ-bound variable is not the one we expected"
 :: ("the variable" , [[ x ]] , [])
 :: (to-string-tag-tk "its declared classifier" Γ atk')
 :: [ to-string-tag-tk "the expected classifier" Γ atk ]) ++ tvs

lambda-bound-class-if : optClass → tk → tk
lambda-bound-class-if NoClass atk = atk
lambda-bound-class-if (SomeClass atk') atk = atk'

var-spans-term : term → spanM ⊤
var-spans-optTerm : optTerm → spanM ⊤
var-spans-term (App t x t') = spanM-add (App-span t t' checking []) ≫span var-spans-term t ≫span var-spans-term t'
var-spans-term (AppTp t x) = var-spans-term t 
var-spans-term (Beta x ot) = var-spans-optTerm ot 
var-spans-term (Chi x x₁ t) = var-spans-term t
var-spans-term (Epsilon x x₁ x₂ t) = var-spans-term t
var-spans-term (Hole x) = spanM-add (hole-span empty-ctxt x nothing [])
var-spans-term (Let pi (DefTerm pi' x m t) t') =
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl pi' x Γ in
      set-ctxt Γ' ≫span
      spanM-add (Let-span Γ checking pi (DefTerm pi' x m t) t' []) ≫span
      spanM-add (Var-span Γ' pi' x untyped []) ≫span
      var-spans-term t ≫span
      var-spans-term t' ≫span      
      set-ctxt Γ)
var-spans-term (Let pi (DefType pi' x k t) t') = 
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl pi' x Γ in
      set-ctxt Γ' ≫span
      spanM-add (Var-span Γ' pi' x untyped []) ≫span
      var-spans-term t' ≫span      
      set-ctxt Γ)
var-spans-term (Lam pi l pi' x _ t) =
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl pi' x Γ in
      set-ctxt Γ' ≫span
      spanM-add (Lam-span Γ checking pi l x NoClass t []) ≫span
      spanM-add (Var-span Γ' pi' x untyped []) ≫span
      var-spans-term t ≫span
      set-ctxt Γ)
var-spans-term (Parens x t x₁) = var-spans-term t
var-spans-term (Phi pi eq t₁ t₂ pi') = var-spans-term eq ≫span var-spans-term t₁ ≫span var-spans-term t₂
var-spans-term (Rho _ _ t t') = var-spans-term t ≫span var-spans-term t'
var-spans-term (Sigma x t) = var-spans-term t
var-spans-term (Theta x x₁ t x₂) = var-spans-term t
var-spans-term (Var pi x) =
  get-ctxt (λ Γ →
    spanM-add (Var-span Γ pi x untyped (if ctxt-binds-var Γ x then []
                                        else [ error-data "This variable is not currently in scope." ])))
var-spans-term (IotaPair _ t1 t2 _) = var-spans-term t1 ≫span var-spans-term t2
var-spans-term (IotaProj t _ _) = var-spans-term t

var-spans-optTerm NoTerm = spanMok
var-spans-optTerm (SomeTerm t _) = var-spans-term t


{- for check-term and check-type, if the optional classifier is given, we will check against it.
   Otherwise, we will try to synthesize a type.  

   check-termi does not have to worry about normalizing the type it is given or the one it
   produces, nor about instantiating with the subject.  This will be handled by interleaved 
   calls to check-term.

   check-type should return kinds in hnf using check-type-return.

   Use add-tk above to add declarations to the ctxt, since these should be normalized
   and with self-types instantiated.
 -}
{-# TERMINATING #-}
check-term : term → (m : maybe type) → spanM (check-ret m)
check-termi : term → (m : maybe type) → spanM (check-ret m)
check-term-app : term → (m : maybe type) → spanM (maybe (meta-vars × type))
check-type : type → (m : maybe kind) → spanM (check-ret m)
check-typei : type → (m : maybe kind) → spanM (check-ret m)
check-kind : kind → spanM ⊤
check-tk : tk → spanM ⊤

check-term subject nothing = check-termi subject nothing ≫=span cont
  where cont : maybe type → spanM (maybe type)
        cont (just tp) = get-ctxt (λ Γ → spanMr (just (hnf Γ unfold-head tp tt)))
        cont nothing = spanMr nothing 
check-term subject (just tp) =
  get-ctxt (λ Γ →
    check-termi subject (just (hnf Γ (if is-intro-form subject then unfold-head-rec-defs else unfold-head) tp tt)))

check-type subject nothing = check-typei subject nothing
check-type subject (just k) = get-ctxt (λ Γ → check-typei subject (just (hnf Γ unfold-head k tt)))

check-termi (Parens pi t pi') tp =
  spanM-add (punctuation-span "Parens" pi pi') ≫span
  check-termi t tp
check-termi (Var pi x) mtp =
  get-ctxt (cont mtp)
  where cont : (mtp : maybe type) → ctxt → spanM (check-ret mtp)
        cont mtp Γ with ctxt-lookup-term-var Γ x
        cont mtp Γ | nothing = 
         spanM-add (Var-span Γ pi x (maybe-to-checking mtp)
                      (error-data "Missing a type for a term variable." :: 
                       expected-type-if Γ mtp ++ (missing-type :: []))) ≫span
         return-when mtp mtp
        cont nothing Γ | just tp = 
          spanM-add (Var-span Γ pi x synthesizing (type-data Γ tp :: [ hnf-type Γ tp ])) ≫span
          check-termi-return Γ (Var pi x) tp
        cont (just tp) Γ | just tp' = 
          spanM-add (Var-span Γ pi x checking (check-for-type-mismatch Γ "synthesized" tp tp'))

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
         spanM-add (Let-span Γ (maybe-to-checking mtp) pi d t []) ≫span
         check-term t mtp ≫=span λ r →
         spanM-restore-info x m ≫span
         spanMr r)

        add-def : defTermOrType → spanM (var × restore-def)
        add-def (DefTerm pi₁ x NoCheckType t') =
           get-ctxt λ Γ → check-term t' nothing ≫=span cont (compileFail-in Γ t') t'
          where cont : 𝕃 tagged-val → term → maybe type → spanM (var × restore-def)
                cont tvs t' (just T) = spanM-push-term-def pi₁ x t' T ≫=span λ m →
                                     get-ctxt λ Γ → 
                                       spanM-add (Var-span Γ pi₁ x synthesizing (type-data Γ T :: tvs)) ≫span
                                     spanMr (x , m)
                cont tvs t' nothing = spanM-push-term-udef pi₁ x t' ≫=span λ m →
                                    get-ctxt λ Γ →
                                      spanM-add (Var-span Γ pi₁ x synthesizing tvs) ≫span
                                    spanMr (x , m)
        add-def (DefTerm pi₁ x (Type T) t') =
          check-type T (just star) ≫span
          get-ctxt λ Γ →
          let T' = qualif-type Γ T in
          check-term t' (just T') ≫span 
          spanM-push-term-def pi₁ x t' T' ≫=span λ m →
          get-ctxt λ Γ →
            spanM-add (Var-span Γ pi₁ x checking (type-data Γ T' :: compileFail-in Γ t')) ≫span
          spanMr (x , m)
        add-def (DefType pi x k T) =
          check-kind k ≫span
          get-ctxt λ Γ →
          let k' = qualif-kind Γ k in
          check-type T (just k') ≫span
          spanM-push-type-def pi x T k' ≫=span λ m →
          get-ctxt λ Γ → spanM-add (Var-span Γ pi x checking [ kind-data Γ k' ]) ≫span
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
           spanM-add (Lam-span Γ synthesizing pi l x (SomeClass atk) t []) ≫span 
                       spanMr nothing)
        cont (just tp) =
          get-ctxt (λ Γ → 
           let atk' = qualif-tk Γ atk in
           -- This should indeed "unqualify" occurrences of x in tp for rettp
           let rettp = abs-tk l x pi' atk' (rename-type Γ (pi' % x) x (tk-is-type atk) tp) in
           let tvs = [ type-data Γ rettp ] in
           spanM-add (Lam-span Γ synthesizing pi l x (SomeClass atk') t 
                       (if (lam-is-erased l) && (is-free-in skip-erased x t) then
                           (error-data "The bound variable occurs free in the erasure of the body (not allowed)."
                         :: erasure Γ t :: tvs)
                        else tvs)) ≫span
           check-termi-return Γ (Lam pi l pi' x (SomeClass atk) t) rettp)

check-termi (Lam pi l _ x NoClass t) nothing =
  get-ctxt (λ Γ → 
    spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
    spanM-add (Lam-span Γ synthesizing pi l x NoClass t
                [ error-data ("We are not checking this abstraction against a type, so a classifier must be"
                            ^ " given for the bound variable " ^ x) ]) ≫span
    spanMr nothing)

check-termi (Lam pi l pi' x oc t) (just tp) with to-abs tp 
check-termi (Lam pi l pi' x oc t) (just tp) | just (mk-abs pi'' b pi''' x' atk _ tp') =
  check-oc oc ≫span
  spanM-add (punctuation-span "Lambda" pi (posinfo-plus pi 1)) ≫span
  get-ctxt (λ Γ → 
    spanM-add (this-span Γ atk oc (check-erasures Γ l b)) ≫span
    (add-tk' (lam-is-erased l) localScope pi' x (lambda-bound-class-if oc atk)) ≫=span λ mi → 
    get-ctxt (λ Γ' → check-term t (just (rename-type Γ x' (qualif-var Γ' x) (tk-is-type atk) tp'))) ≫span
    spanM-restore-info x mi) 
  where this-span : ctxt → tk → optClass → 𝕃 tagged-val → span
        this-span Γ _ NoClass tvs = Lam-span Γ checking pi l x oc t tvs
        this-span Γ atk (SomeClass atk') tvs = 
          if conv-tk Γ (qualif-tk Γ atk') atk then
            Lam-span Γ checking pi l x oc t tvs
          else
            Lam-span Γ checking pi l x oc t (lambda-bound-var-conv-error Γ x atk atk' tvs)
        check-oc : optClass → spanM ⊤
        check-oc NoClass = spanMok
        check-oc (SomeClass atk) = check-tk atk
        check-erasures : ctxt → lam → binder → 𝕃 tagged-val
        check-erasures Γ ErasedLambda All = type-data Γ tp 
                                       :: (if (is-free-in skip-erased x t) then 
                                            (error-data "The Λ-bound variable occurs free in the erasure of the body." 
                                            :: [ erasure Γ t ])
                                           else [])
        check-erasures Γ KeptLambda Pi = [ type-data Γ tp ]
        check-erasures Γ ErasedLambda Pi = error-data ("The expected type is a Π-abstraction (indicating explicit input), but"
                                              ^ " the term is a Λ-abstraction (implicit input).")
                                     :: [ expected-type Γ tp ]
        check-erasures Γ KeptLambda All = error-data ("The expected type is a ∀-abstraction (indicating implicit input), but"
                                              ^ " the term is a λ-abstraction (explicit input).")
                                     :: [ expected-type Γ tp ]
check-termi (Lam pi l pi' x oc t) (just tp) | nothing =
   get-ctxt (λ Γ →
    spanM-add (punctuation-span "Lambda"  pi (posinfo-plus pi 1)) ≫span
    spanM-add (Lam-span Γ checking pi l x oc t (error-data "The expected type is not of the form that can classify a λ-abstraction" ::
                   expected-type Γ tp :: [])))


check-termi (Beta pi ot) (just (TpEq t1 t2)) = 
  var-spans-optTerm ot ≫span
  get-ctxt (λ Γ → 
    if conv-term Γ t1 t2 then
      spanM-add (Beta-span pi (optTerm-end-pos (posinfo-plus pi 1) ot)
                   checking [ type-data Γ (TpEq t1 t2) ])
    else
      spanM-add (Beta-span pi (optTerm-end-pos (posinfo-plus pi 1) ot)
                  checking (error-data "The two terms in the equation are not β-equal" :: [ expected-type Γ (TpEq t1 t2) ])))

check-termi (Beta pi ot) (just tp) = 
  get-ctxt (λ Γ → 
   var-spans-optTerm ot ≫span
   spanM-add (Beta-span pi (optTerm-end-pos (posinfo-plus pi 1) ot) checking (error-data "The expected type is not an equation." :: [ expected-type Γ tp ])))

check-termi (Beta pi ot) nothing = 
  var-spans-optTerm ot ≫span
  spanM-add (Beta-span pi (optTerm-end-pos (posinfo-plus pi 1) ot) synthesizing [ error-data "An expected type is required in order to type a use of β." ]) ≫span spanMr nothing

check-termi (Epsilon pi lr m t) (just (TpEq t1 t2)) = 
  get-ctxt (λ Γ → 
  spanM-add (Epsilon-span pi lr m t checking [ type-data Γ (TpEq t1 t2) ]) ≫span
    check-term t (just (check-term-update-eq Γ lr m t1 t2)))

check-termi (Epsilon pi lr m t) (just tp) = 
  get-ctxt (λ Γ → 
  spanM-add (Epsilon-span pi lr m t checking (error-data ("The expected type is not an equation, when checking an ε-term.") 
                                        :: [ expected-type Γ tp ])) ≫span 
  spanMok)
check-termi (Epsilon pi lr m t) nothing = 
  check-term t nothing ≫=span cont
  where cont : maybe type → spanM (maybe type)
        cont nothing = 
          spanM-add (Epsilon-span pi lr m t synthesizing [ error-data ("There is no expected type, and we could not synthesize a type from the body"
                                                           ^ " of the ε-term.") ]) ≫span
          spanMr nothing
        cont (just (TpEq t1 t2)) =
          get-ctxt (λ Γ → 
            let r = check-term-update-eq Γ lr m t1 t2 in
            spanM-add (Epsilon-span pi lr m t synthesizing [ type-data Γ r ]) ≫span
            spanMr (just r))
        cont (just tp) = 
          get-ctxt (λ Γ → 
          spanM-add (Epsilon-span pi lr m t synthesizing ( error-data ("There is no expected type, and the type we synthesized for the body"
                                                           ^ " of the ε-term is not an equation.")
                                             :: [ to-string-tag "the synthesized type" Γ tp ])) ≫span
          spanMr nothing)

check-termi (Sigma pi t) mt = 
  check-term t nothing ≫=span cont mt
  where cont : (outer : maybe type) → maybe type → spanM (check-ret outer)
        cont mt nothing = 
          get-ctxt (λ Γ → 
          spanM-add (Sigma-span Γ pi t mt [ error-data ("We could not synthesize a type from the body"
                                                    ^ " of the ς-term.") ]) ≫span
          check-fail mt)
        cont mt (just (TpEq t1 t2)) with TpEq t2 t1 
        cont nothing (just (TpEq t1 t2)) | r =
          get-ctxt (λ Γ → 
          spanM-add (Sigma-span Γ pi t nothing [ type-data Γ r ]) ≫span
          spanMr (just r))
        cont (just tp) (just (TpEq t1 t2)) | r =
          get-ctxt (λ Γ → 
            spanM-add (Sigma-span Γ pi t (just tp) (check-for-type-mismatch Γ "synthesized" tp r)))
        cont mt (just tp) = 
          get-ctxt (λ Γ → 
          spanM-add (Sigma-span Γ pi t mt ( error-data ("The type we synthesized for the body"
                                                      ^ " of the ς-term is not an equation.")
                                          :: [ to-string-tag "the synthesized type" Γ tp ])) ≫span
          check-fail mt)

check-termi (Phi pi t₁≃t₂ t₁ t₂ pi') (just tp) =
  get-ctxt (λ Γ →
    check-term t₁≃t₂ (just (qualif-type Γ (TpEq t₁ t₂)))) ≫span
  check-term t₁ (just tp) ≫span
  var-spans-term t₂ ≫span
  get-ctxt (λ Γ → spanM-add (Phi-span pi pi' checking [ type-data Γ tp ]))

check-termi (Phi pi t₁≃t₂ t₁ t₂ pi') nothing =
  get-ctxt (λ Γ →
    check-term t₁≃t₂ (just (qualif-type Γ (TpEq t₁ t₂)))) ≫span
  check-term t₁ nothing ≫=span λ mtp →
  var-spans-term t₂ ≫span
  get-ctxt (λ Γ → spanM-add
    (Phi-span pi pi' synthesizing (type-data-tvs Γ mtp))) ≫span
  spanMr mtp
    where
      type-data-tvs : ctxt → maybe type → 𝕃 tagged-val
      type-data-tvs Γ (just tp) = type-data Γ tp :: [ hnf-type Γ tp ]
      type-data-tvs Γ nothing = []

check-termi (Rho pi r t t') (just tp) = 
  check-term t nothing ≫=span cont
  where cont : maybe type → spanM ⊤
        cont nothing = get-ctxt (λ Γ → spanM-add (Rho-span pi t t' checking r 0 [ expected-type Γ tp ]) ≫span check-term t' (just tp))
        cont (just (TpEq t1 t2)) = 
           get-ctxt (λ Γ →
             let s = rewrite-type Γ empty-renamectxt (is-rho-plus r) t1 t2 tp in
             check-term t' (just (fst s)) ≫span
             get-ctxt (λ Γ →
             spanM-add (Rho-span pi t t' checking r (snd s) ( (to-string-tag "the equation" Γ (TpEq t1 t2)) :: [ type-data Γ tp ]))))
        cont (just tp') =
          get-ctxt (λ Γ → spanM-add (Rho-span pi t t' checking r 0
                                       (error-data "We could not synthesize an equation from the first subterm in a ρ-term."
                                     :: (to-string-tag "the synthesized type for the first subterm" Γ tp')
                                     :: [ expected-type Γ tp ])))

check-termi (Rho pi r t t') nothing = 
  check-term t nothing ≫=span λ mtp → 
  check-term t' nothing ≫=span cont mtp
  where cont : maybe type → maybe type → spanM (maybe type)
        cont (just (TpEq t1 t2)) (just tp) = 
          get-ctxt (λ Γ → 
            let s = rewrite-type Γ empty-renamectxt (is-rho-plus r) t1 t2 tp in
            let tp' = fst s in
              spanM-add (Rho-span pi t t' synthesizing r (snd s) [ type-data Γ tp' ]) ≫span
              check-termi-return Γ (Rho pi r t t') tp')
        cont (just tp') m2 =
           get-ctxt (λ Γ → spanM-add (Rho-span pi t t' synthesizing r 0
                                         (error-data "We could not synthesize an equation from the first subterm in a ρ-term."
                                      :: (to-string-tag "the synthesized type for the first subterm" Γ tp')
                                      :: [])) ≫span spanMr nothing)
        cont nothing _ = spanM-add (Rho-span pi t t' synthesizing r 0 []) ≫span spanMr nothing

check-termi (Chi pi (Atype tp) t) mtp =
  check-type tp (just star) ≫span
  get-ctxt λ Γ →
  let tp' = qualif-type Γ tp in
  check-termi t (just tp') ≫span cont tp' mtp
  where cont : type → (m : maybe type) → spanM (check-ret m)
        cont tp' nothing = get-ctxt (λ Γ → spanM-add (Chi-span Γ pi (Atype tp) t synthesizing []) ≫span spanMr (just tp'))
        cont tp' (just tp'') =
          get-ctxt (λ Γ → 
           spanM-add (Chi-span Γ pi (Atype tp') t checking (check-for-type-mismatch Γ "asserted" tp'' tp')))
check-termi (Chi pi NoAtype t) (just tp) = 
  check-term t nothing ≫=span cont 
  where cont : (m : maybe type) → spanM ⊤
        cont nothing = get-ctxt (λ Γ → spanM-add (Chi-span Γ pi NoAtype t checking []) ≫span spanMok)
        cont (just tp') =
          get-ctxt (λ Γ → 
            spanM-add (Chi-span Γ pi NoAtype t checking (check-for-type-mismatch Γ "synthesized" tp tp')))
check-termi (Chi pi NoAtype t) nothing =
 get-ctxt λ Γ → spanM-add (Chi-span Γ pi NoAtype t synthesizing []) ≫span check-term t nothing

check-termi (Theta pi u t ls) nothing =
  get-ctxt (λ Γ →
  spanM-add (Theta-span Γ pi u t ls synthesizing
               [ error-data "Theta-terms can only be used in checking positions (and this is a synthesizing one)." ])
  ≫span spanMr nothing)

check-termi (Theta pi AbstractEq t ls) (just tp) =
  -- discard spans from checking t, because we will check it again below
  check-term t nothing ≫=spand cont
  where cont : maybe type → spanM ⊤
        cont nothing = check-term t nothing ≫=span (λ m → 
                       get-ctxt (λ Γ →
                          spanM-add (Theta-span Γ pi AbstractEq t ls checking
                                      (expected-type Γ tp :: [ motive-label , [[ "We could not compute a motive from the given term" ]] , [] ]))))
        cont (just htp) =
           get-ctxt (λ Γ → 
             let x = (fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt) in
             let motive = mtplam x (Tkt htp) (TpArrow (TpEq t (mvar x)) UnerasedArrow tp) in
               spanM-add (Theta-span Γ pi AbstractEq t ls checking (expected-type Γ tp :: [ the-motive Γ motive ])) ≫span 
               check-term (App* (AppTp t (NoSpans motive (posinfo-plus (term-end-pos t) 1)))
                              (lterms-to-𝕃 AbstractEq ls))
                 (just tp))

check-termi (Theta pi Abstract t ls) (just tp) =
  -- discard spans from checking the head, because we will check it again below
  check-term t nothing ≫=spand cont t
  where cont : term → maybe type → spanM ⊤
        cont _ nothing = check-term t nothing ≫=span (λ m → 
                         get-ctxt (λ Γ →
                           spanM-add (Theta-span Γ pi Abstract t ls checking
                                      (expected-type Γ tp :: [ motive-label , [[ "We could not compute a motive from the given term" ]] , [] ]))))
        cont t (just htp) = 
          let x = compute-var t in
          let motive = mtplam x (Tkt htp) tp in
           get-ctxt (λ Γ →
            spanM-add (Theta-span Γ pi Abstract t ls checking (expected-type Γ tp :: [ the-motive Γ motive ])) ≫span 
            check-term (App* (AppTp t (NoSpans motive (term-end-pos t)))
                            (lterms-to-𝕃 Abstract ls)) 
               (just tp))
          where compute-var : term → string
                compute-var (Var pi' x) = x
                compute-var t = ignored-var

check-termi (Theta pi (AbstractVars vs) t ls) (just tp) =
  get-ctxt (λ Γ → cont (wrap-vars Γ vs (substs-type (new-ctxt "" "") (rep-vars Γ vs empty-trie) tp)))
  where wrap-var : ctxt → var → type → maybe type
        wrap-var Γ v tp = ctxt-lookup-tk-var Γ v ≫=maybe (λ atk → just (mtplam v atk tp))
        wrap-vars : ctxt → vars → type → maybe type
        wrap-vars Γ (VarsStart v) tp = wrap-var Γ v tp
        wrap-vars Γ (VarsNext v vs) tp = wrap-vars Γ vs tp ≫=maybe (λ tp → wrap-var Γ v tp)
        cont : maybe type → spanM ⊤
        cont nothing = check-term t nothing ≫=span (λ m → 
                       get-ctxt (λ Γ →
                          spanM-add (Theta-span Γ pi (AbstractVars vs) t ls checking
                                      (expected-type Γ tp :: [ error-data ("We could not compute a motive from the given term"
                                                                       ^ " because one of the abstracted vars is not in scope.") ]))))
        cont (just motive) =
           get-ctxt (λ Γ →
            spanM-add (Theta-span Γ pi (AbstractVars vs) t ls checking (expected-type Γ tp :: [ the-motive Γ motive ])) ≫span 
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

check-termi (IotaPair pi t1 t2 pi') (just (Iota pi1 pi2 x (SomeType tp1) tp2)) =
  check-term t1 (just tp1) ≫span
  get-ctxt (λ Γ → 
    let t1' = qualif-term Γ t1 in
    let t2' = qualif-term Γ t2 in
    check-term t2 (just (subst-type Γ t1' x tp2)) ≫span
    -- TODO why another get-ctxt here?
    get-ctxt (λ Γ → 
    spanM-add (IotaPair-span pi pi' checking (expected-type Γ (Iota pi1 pi2 x (SomeType tp1) tp2) :: (check-conv Γ t1' t2')))))
  where ntag : ctxt → string → string → term → unfolding → tagged-val
        ntag Γ nkind which t u = to-string-tag (nkind ^ " of the " ^ which ^ " component: ") Γ (hnf Γ u t tt)
        err : ctxt → string → term → 𝕃 tagged-val
        err Γ which t =
          ntag Γ "Hnf" which t unfold-head :: [] -- [ ntag Γ "Nf" which t unfold-all ]
        check-conv : ctxt → term → term → 𝕃 tagged-val
        check-conv Γ t1 t2 =
                (if conv-term Γ t1 t2 then
                  []
                 else ((error-data "The two components of the iota-pair are not convertible (as required)." ) ::
                       (err Γ "first" t1) ++ (err Γ "second" t2)))

check-termi (IotaPair pi t1 t2 pi') (just tp) =
  get-ctxt (λ Γ →
  spanM-add (IotaPair-span pi pi' checking (expected-type Γ tp :: [ error-data "The type we are checking against is not a iota-type" ])))

check-termi (IotaPair pi t1 t2 pi') nothing =
  spanM-add (IotaPair-span pi pi' synthesizing [ error-data "Iota pairs can only be used in a checking position" ]) ≫span
  spanMr nothing


check-termi (IotaProj t n pi) mtp =
  check-term t nothing ≫=span cont' mtp (num-to-ℕ n)
  where cont : (outer : maybe type) → ℕ → (computed : type) → spanM (check-ret outer)
        cont mtp n computed with computed
        cont mtp 1 computed | Iota pi' pi'' x NoType t2 =
           get-ctxt (λ Γ →
            spanM-add (IotaProj-span t pi (maybe-to-checking mtp)
                        (error-data "The head type is a iota-type, but it has no first component." ::
                              [ head-type Γ computed ] )) ≫span
            return-when mtp mtp)
        cont mtp 1 computed | Iota pi' pi'' x (SomeType t1) t2 =
          get-ctxt (λ Γ →
            spanM-add (IotaProj-span t pi (maybe-to-checking mtp) (head-type Γ computed ::
                                           check-for-type-mismatch-if Γ "synthesized" mtp t1)) ≫span
            return-when mtp (just t1))
        cont mtp 2 computed | Iota pi' pi'' x a t2 =
          get-ctxt (λ Γ →
            let t2' = subst-type Γ (qualif-term Γ t) x t2 in
              spanM-add (IotaProj-span t pi (maybe-to-checking mtp)
                          (head-type Γ computed :: check-for-type-mismatch-if Γ "synthesized" mtp t2')) ≫span
              return-when mtp (just t2'))
        cont mtp n computed | Iota pi' pi'' x t1 t2 =
          get-ctxt (λ Γ →
          spanM-add (IotaProj-span t pi (maybe-to-checking mtp) ( error-data "Iota-projections must use .1 or .2 only."
                                      :: [ head-type Γ computed ])) ≫span return-when mtp mtp)
        cont mtp n computed | _ =
          get-ctxt (λ Γ →
          spanM-add (IotaProj-span t pi (maybe-to-checking mtp) ( error-data "The head type is not a iota-abstraction."
                                        :: [ head-type Γ computed ])) ≫span return-when mtp mtp)
        cont' : (outer : maybe type) → ℕ → (computed : maybe type) → spanM (check-ret outer)
        cont' mtp _ nothing = spanM-add (IotaProj-span t pi (maybe-to-checking mtp) []) ≫span return-when mtp mtp
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
      (App-span t t' m
        ((error-data
          ("The type computed for the head of the application does"
          ^ " not allow the head to be applied to " ^ h e ^ " argument ")
        :: term-app-head Γ t :: head-type Γ (meta-vars-subst-type Γ Xs htp)
        :: [ term-argument Γ t' ])))
  where h : maybeErased → string
        h Erased = "an erased term"
        h NotErased = "a term"

check-term-app-error-unmatchable : ∀ {A} ctxt → (ht t : term) (htpₓ tp : type)
                                   → meta-vars → checking-mode → string → spanM (maybe A)
check-term-app-error-unmatchable Γ tₓ t tpₓ tp Xs cm msg
  =   spanM-add (App-span tₓ t cm
        (error-data msg :: arg-exp-type Γ tpₓ :: arg-type Γ tp
          :: meta-vars-data Γ Xs))
    ≫span spanMr nothing

check-term-app-error-erased : ∀ {A} checking-mode → maybeErased
                              → (t t' : term) → type → meta-vars → spanM (maybe A)
check-term-app-error-erased c m t t' htp Xs
  =   get-ctxt λ Γ → spanM-add
        (App-span t t' c
          (error-data (msg m) :: term-app-head Γ t
          :: [ head-type Γ (meta-vars-subst-type Γ Xs htp )]))
    ≫span spanMr nothing
  where msg : maybeErased → string
        msg Erased = ("The type computed for the head requires"
                    ^ " an explicit (non-erased) argument, but the application"
                    ^ " is marked as erased")
        msg NotErased = ("The type computed for the head requires"
                    ^ " an implicit (erased) argument, but the application"
                    ^ " is marked as not erased")

-- main definition
check-term-app t''@(App t m t') mtp
  -- check head
  =   check-term-app t nothing
    on-fail (spanM-add (App-span t t' check-mode [])
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
      case meta-vars-unfold-tmapp' Γ Xs tp of λ where
        (Xs , yes-arrow-or-abs tp tpₐ m' cod) →
          if ~ check-erasures-match m m'
            then check-term-app-error-erased check-mode m t t' tp Xs
          else if ~ meta-vars-are-free-in-type Xs tpₐ
            then   check-term t' (just tpₐ)
                 ≫span spanM-add
                   (App-span t t' check-mode
                     ((meta-vars-check-type-mismatch-if mtp Γ "synthesized" Xs (cod t'))))
                 ≫span check-term-app-return Γ t'' Xs (cod t')
          else   check-term t' nothing
               on-fail   spanM-add (App-span t t' check-mode
                           ([ head-type Γ (meta-vars-subst-type Γ Xs tp)]))
                      ≫span spanMr nothing
               ≫=spanm' λ tpₐ' → case meta-vars-match Γ Xs empty-trie tpₐ tpₐ' of λ where
                 (yes-error msg) →
                   check-term-app-error-unmatchable Γ t t' tpₐ tpₐ' Xs check-mode msg
                 (no-error   Xs) →
                     spanM-add (App-span t t' check-mode
                       (arg-exp-type Γ tpₐ
                       :: arg-type Γ tpₐ'
                       :: ((meta-vars-check-type-mismatch-if mtp Γ "synthesized" Xs (cod t')))))
                   ≫span check-term-app-return Γ t'' Xs (cod t')
        (Xs , not-arrow-or-abs tp) →
            check-term-app-error-inapp Γ t t' tp Xs check-mode m
          ≫span spanMr nothing 

check-term-app (AppTp t tp) mtp
  -- check head
  =   check-term-app t nothing
        on-fail spanM-add ((AppTp-span t tp check-mode []))
          ≫span spanMr nothing
    ≫=spanm' λ {(Xs , htp) → get-ctxt λ Γ →
      -- check agreement (trying the unsolved head type first)
      check-term-app-agree (hnf Γ unfold-head-rec-defs htp tt) tp Xs
        on-fail (check-term-app-to-tp-error Γ Xs htp)
    ≫=spanm' λ {ret@(Xs , tp') → get-ctxt λ Γ →
      spanM-add (AppTp-span t tp check-mode
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
          (inj₁ _) → spanMr nothing
          (inj₂ (tp-is-kind-abs pi b pi' x k htp')) →
              -- TODO avoid double substitution
              check-type tp (just (meta-vars-subst-kind Γ Xs k))
            ≫span get-ctxt λ Γ →
              let X    = meta-vars-fresh Xs x k [ qualif-type Γ tp ]
                  htp″ = subst-type Γ (TpVar pi' (meta-var-name X)) x htp'
                  Xs'  = meta-vars-add Xs X
              in spanMr (just (meta-vars-add Xs X , htp″))

    -- TODO bring into check-term-app-error-inapp
    check-term-app-to-tp-error : ctxt → meta-vars → type → spanM _
    check-term-app-to-tp-error Γ Xs htp = get-ctxt
      λ Γ → spanM-add ((AppTp-span t tp synthesizing
              (error-data ("The type computed for the head of the application does"
                           ^ " not allow the head to be applied to the (type) argument ")
              :: term-app-head Γ t
              :: head-type Γ (meta-vars-subst-type Γ Xs htp)
              :: type-argument Γ tp :: [])))
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
                       (error-data "Missing a kind for a type variable." :: 
                        expected-kind-if Γ mk ++ (missing-kind :: []))) ≫span
          return-when mk mk
        cont nothing Γ | (just k) = 
          spanM-add (TpVar-span Γ pi x synthesizing ((kind-data Γ k) :: [])) ≫span
          check-type-return Γ k
        cont (just k) Γ | just k' = 
         if conv-kind Γ k k' 
         then spanM-add (TpVar-span Γ pi x checking
                          (expected-kind Γ k :: [ kind-data Γ k' ]))
         else spanM-add (TpVar-span Γ pi x checking
                           (error-data "The computed kind does not match the expected kind." :: 
                            expected-kind Γ k ::
                            [ kind-data Γ k' ]))
check-typei (TpLambda pi pi' x atk body) (just k) with to-absk k 
check-typei (TpLambda pi pi' x atk body) (just k) | just (mk-absk pik pik' x' atk' _ k') =
   check-tk atk ≫span
   spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
   get-ctxt (λ Γ → 
   spanM-add (if conv-tk Γ (qualif-tk Γ atk) atk' then
                TpLambda-span pi x atk body checking [ kind-data Γ k ]
              else
                TpLambda-span pi x atk body checking (lambda-bound-var-conv-error Γ x atk' atk [ kind-data Γ k ])) ≫span
   add-tk pi' x atk ≫=span λ mi → 
   get-ctxt (λ Γ' → check-type body (just (rename-kind Γ x' (qualif-var Γ' x) (tk-is-type atk') k'))) ≫span
   spanM-restore-info x mi)
check-typei (TpLambda pi pi' x atk body) (just k) | nothing = 
   check-tk atk ≫span
   spanM-add (punctuation-span "Lambda (type)" pi (posinfo-plus pi 1)) ≫span
   get-ctxt (λ Γ →
   spanM-add (TpLambda-span pi x atk body checking
               (error-data "The type is being checked against a kind which is not an arrow- or Pi-kind." ::
                expected-kind Γ k :: [])))

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
          spanM-add (TpLambda-span pi x atk body synthesizing []) ≫span
          spanMr nothing
        cont (just k) =
             get-ctxt (λ Γ →
              let atk' = qualif-tk Γ atk in
              -- This should indeed "unqualify" occurrences of x in k for r
              let r = absk-tk x pi' atk' (rename-kind Γ (pi' % x) x (tk-is-type atk) k) in
              spanM-add (TpLambda-span pi x atk' body synthesizing [ kind-data Γ r ]) ≫span
              spanMr (just r))

check-typei (Abs pi b {- All or Pi -} pi' x atk body) k = 
  get-ctxt (λ Γ →
  spanM-add (TpQuant-span (binder-is-pi b) pi x atk body (maybe-to-checking k)
               (if-check-against-star-data Γ "A type-level quantification" k)) ≫span
  spanM-add (punctuation-span "Forall" pi (posinfo-plus pi 1)) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  check-type body (just star) ≫span
  spanM-restore-info x mi ≫span
  return-star-when k)

check-typei (TpArrow t1 _ t2) k = 
  get-ctxt (λ Γ →
  spanM-add (TpArrow-span t1 t2 (maybe-to-checking k) (if-check-against-star-data Γ "An arrow type" k)) ≫span
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
                               (error-data ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a term")
                            :: type-app-head Γ tp
                            :: head-kind Γ k' 
                            :: term-argument Γ t
                            :: [])) ≫span
                  spanMr nothing)
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          get-ctxt (λ Γ →
          spanM-add (TpAppt-span tp t synthesizing ((kind-data Γ k) :: [])) ≫span
            check-type-return Γ k)
        cont' (just k') k = 
          get-ctxt (λ Γ → 
            if conv-kind Γ k k' then spanM-add (TpAppt-span tp t checking (expected-kind Γ k' :: [ kind-data Γ k ]))
            else spanM-add (TpAppt-span tp t checking 
                           (error-data "The kind computed for a type application does not match the expected kind." ::
                            expected-kind Γ k' ::
                            kind-data Γ k ::
                            [])))
        cont'' : maybe kind → spanM (maybe kind)
        cont'' nothing = spanM-add (TpAppt-span tp t (maybe-to-checking k) []) ≫span spanMr nothing
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
                               (error-data ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a type")
                            :: type-app-head Γ tp
                            :: head-kind Γ k' 
                            :: type-argument Γ tp'
                            :: [])) ≫span
                  spanMr nothing)
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          get-ctxt (λ Γ → 
          spanM-add (TpApp-span tp tp' synthesizing ((kind-data Γ k) :: [])) ≫span
            check-type-return Γ k)
        cont' (just k') k = 
          get-ctxt (λ Γ → 
            if conv-kind Γ k k' then spanM-add (TpApp-span tp tp' checking (expected-kind Γ k' :: [ kind-data Γ k' ]))
            else spanM-add (TpApp-span tp tp' checking 
                           (error-data "The kind computed for a type application does not match the expected kind." ::
                            expected-kind Γ k' ::
                            kind-data Γ k ::
                            [])))
        cont'' : maybe kind → spanM (maybe kind)
        cont'' nothing = spanM-add (TpApp-span tp tp' (maybe-to-checking k) []) ≫span spanMr nothing
        cont'' (just k) = cont k

check-typei (TpEq t1 t2) k = 
  get-ctxt (λ Γ → 
    var-spans-term t1 ≫span
    set-ctxt Γ ≫span 
    var-spans-term t2 ≫span
    set-ctxt Γ) ≫span 
    get-ctxt (λ Γ → 
    spanM-add (TpEq-span t1 t2 (maybe-to-checking k) (if-check-against-star-data Γ "An equation" k)) ≫span
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
        cont nothing k = get-ctxt (λ Γ → spanM-add (Lft-span pi X t synthesizing [ kind-data Γ k ]) ≫span spanMr (just k))
        cont (just k') k = 
          get-ctxt (λ Γ → 
            if conv-kind Γ k k' then 
              spanM-add (Lft-span pi X t checking ( expected-kind Γ k' :: [ kind-data Γ k ])) ≫span spanMok
            else
              spanM-add (Lft-span pi X t checking ( error-data "The expected kind does not match the computed kind."
                                                 :: expected-kind Γ k' :: [ kind-data Γ k ])))
check-typei (Iota pi pi' x (SomeType t1) t2) mk =
  get-ctxt (λ Γ → 
  spanM-add (Iota-span pi t2 (if-check-against-star-data Γ "A iota-type" mk)) ≫span
  check-typei t1 (just star) ≫span
  add-tk pi' x (Tkt t1) ≫=span λ mi → 
  check-typei t2 (just star) ≫span
  spanM-restore-info x mi ≫span
  return-star-when mk)

check-typei (Iota pi pi' x NoType t2) mk =
  get-ctxt (λ Γ → 
  spanM-add (Iota-span pi t2 (error-data "Iota-abstractions in source text require a type for the bound variable."
                          :: (if-check-against-star-data Γ "A iota-type" mk))) ≫span
  return-star-when mk)

check-kind (KndParens pi k pi') =
  spanM-add (punctuation-span "Parens (kind)" pi pi') ≫span
  check-kind k
check-kind (Star pi) = spanM-add (Star-span pi checking)
check-kind (KndVar pi x ys) =
  get-ctxt (λ Γ → helper (ctxt-lookup-kind-var-qdef Γ x) ys)
  where helper : maybe (params × kind) → args → spanM ⊤
        helper (just (ps , k)) ys =
          check-args-against-params ps ys ≫=span λ m →
          spanM-restore-info* m
          where check-args-against-params : params → args → spanM (𝕃 (string × restore-def))
                check-args-against-params (ParamsCons (Decl _ pi x (Tkk k) _) ps) (ArgsCons (TypeArg T) ys) =
                  check-type T (just k) ≫span
                  spanM-push-type-def pi x T k ≫=span λ m → 
                  check-args-against-params ps ys ≫=span λ ms →
                  spanMr ((x , m) :: ms)
                check-args-against-params (ParamsCons (Decl _ pi x (Tkt T) _) ps) (ArgsCons (TermArg t) ys) =
                  check-term t (just T) ≫span
                  spanM-push-term-def pi x t T ≫=span λ m → 
                  check-args-against-params ps ys ≫=span λ ms →
                  spanMr ((x , m) :: ms)
                check-args-against-params (ParamsCons (Decl _ x₁ x (Tkk x₃) x₄) ps₁) (ArgsCons (TermArg x₅) ys₂) =
                  get-ctxt (λ Γ → 
                  spanM-add (KndVar-span Γ pi x ys checking
                               ( error-data ("A term argument was supplied for type parameter " ^ x ^ " of the defined kind.") ::
                                 [ term-argument Γ x₅ ]))) ≫span
                  spanMr []
                check-args-against-params (ParamsCons (Decl _ x₁ x (Tkt x₃) x₄) ps₁) (ArgsCons (TypeArg x₅) ys₂) = 
                  get-ctxt (λ Γ → 
                  spanM-add (KndVar-span Γ pi x ys checking
                               ( error-data ("A type argument was supplied for type parameter " ^ x ^ " of the defined kind.") ::
                                 [ type-argument Γ x₅ ]))) ≫span
                  spanMr []
                check-args-against-params (ParamsCons (Decl _ _ x _ _) ps₁) (ArgsNil _) =
                  get-ctxt (λ Γ → 
                  spanM-add (KndVar-span Γ pi x ys checking
                               [ error-data ("Missing an argument for parameter " ^ x ^ " of the defined kind.") ])) ≫span
                  spanMr []             
                check-args-against-params ParamsNil (ArgsCons x₁ ys₂) = 
                  get-ctxt (λ Γ → 
                  spanM-add (KndVar-span Γ pi x ys checking
                               (error-data "An extra argument was given to the defined kind" ::
                                [ arg-argument Γ x₁ ]))) ≫span
                  spanMr []                                             
                check-args-against-params ParamsNil (ArgsNil x₁) =
                                  get-ctxt (λ Γ → spanM-add (KndVar-span Γ pi x ys checking [])) ≫span spanMr []
        helper nothing _ = get-ctxt (λ Γ → spanM-add (KndVar-span Γ pi x ys checking [ error-data "Undefined kind variable." ]))
    
check-kind (KndArrow k k') = 
  spanM-add (KndArrow-span k k' checking) ≫span
  check-kind k ≫span
  check-kind k'
check-kind (KndTpArrow t k) = 
  spanM-add (KndTpArrow-span t k checking) ≫span
  check-type t (just star) ≫span
  check-kind k
check-kind (KndPi pi pi' x atk k) = 
  spanM-add (punctuation-span "Pi (kind)" pi (posinfo-plus pi 1)) ≫span
  spanM-add (KndPi-span pi x atk k checking) ≫span
  check-tk atk ≫span
  add-tk pi' x atk ≫=span λ mi → 
  check-kind k ≫span
  spanM-restore-info x mi

check-tk (Tkk k) = check-kind k
check-tk (Tkt t) = check-type t (just star)


