module classify where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import lift
open import rename
open import rewriting
open import spans
open import subst
open import syntax-util
open import to-string

check-ret : ∀{A : Set} → maybe A → Set
check-ret{A} nothing = maybe A
check-ret (just _) = ⊤

infixl 2 _≫=spanr_ 
_≫=spanr_ : ∀{A : Set}{m : maybe A} → spanM (maybe A) → (A → spanM (check-ret m)) → spanM (check-ret m)
_≫=spanr_{m = nothing} = _≫=spanm_
_≫=spanr_{m = just _} = _≫=spanj_

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

-- return the second maybe kind
return-when : ∀{A : Set} → (m : maybe A) → maybe A → spanM (check-ret m)
return-when nothing u = spanMr u
return-when (just _) u = spanMr triv

return-star-when : (m : maybe kind) → spanM (check-ret m)
return-star-when m = return-when m (just star)

if-check-against-star-data : string → maybe kind → 𝕃 tagged-val
if-check-against-star-data desc nothing = [ kind-data star ]
if-check-against-star-data desc (just (Star _)) = [ kind-data star ]
if-check-against-star-data desc (just k) = error-data (desc ^ " is being checked against a kind other than ★")
                                        :: expected-kind k
                                        :: []

check-term-app-erased-error : maybeErased → term → term → type → spanM (maybe type)
check-term-app-erased-error m t t' head-tp =
  spanM-add (App-span t t'
               (error-data (msg m) 
                 :: term-app-head t 
                 :: head-type head-tp
                 :: [])) ≫span
  spanMr nothing
  where msg : maybeErased → string
        msg Erased = ("The type computed for the head requires" 
                    ^ " an explicit (non-erased) argument, but the application"
                    ^ " is marked as erased")
        msg NotErased = ("The type computed for the head requires" 
                    ^ " an implicit (erased) argument, but the application"
                    ^ " is marked as not erased")

check-term-app-matching-erasures : maybeErased → binder → 𝔹
check-term-app-matching-erasures Erased All = tt
check-term-app-matching-erasures NotErased Pi = tt
check-term-app-matching-erasures _ _ = ff

check-term-update-eq : ctxt → leftRight → term → term → type
check-term-update-eq Γ Left t1 t2 = TpEq (hnf Γ unfold-head t1) t2
check-term-update-eq Γ Right t1 t2 = TpEq t1 (hnf Γ unfold-head t2) 
check-term-update-eq Γ Both t1 t2 = TpEq (hnf Γ unfold-head t1) (hnf Γ unfold-head t2) 

{- if the hnf of the type is a Iota type, then instantiate it with the given term.
   We assume types do not reduce with normalization and instantiation to further iota
   types. -}
hnf-instantiate-iota : ctxt → term → type → type
hnf-instantiate-iota Γ subject tp with hnf Γ unfold-head-rec-defs tp
hnf-instantiate-iota Γ subject _ | Iota _ x t = hnf Γ unfold-head (subst-type Γ subject x t)
hnf-instantiate-iota Γ subject _ | tp = tp

add-tk : ctxt → posinfo → var → tk → spanM ctxt
add-tk Γ pi x atk =
  spanM-add (var-span pi x atk) ≫span
  spanMr (helper atk)
  where helper : tk → ctxt
        helper (Tkk k) = ctxt-type-decl x k Γ
        helper (Tkt t) = ctxt-term-decl x t Γ

check-type-return : ctxt → kind → spanM (maybe kind)
check-type-return Γ k = spanMr (just (hnf Γ unfold-head k))

check-termi-return : ctxt → (subject : term) → type → spanM (maybe type)
check-termi-return Γ subject tp = spanMr (just (hnf Γ unfold-head tp))

lambda-bound-var-conv-error : var → tk → tk → 𝕃 tagged-val → 𝕃 tagged-val
lambda-bound-var-conv-error x atk atk' tvs = 
    ( error-data "The classifier given for a λ-bound variable is not the one we expected"
 :: ("the variable" , x)
 :: ("its declared classifier" , tk-to-string atk')
 :: [ "the expected classifier" , tk-to-string atk ]) ++ tvs

lambda-bound-class-if : optClass → tk → tk
lambda-bound-class-if NoClass atk = atk
lambda-bound-class-if (SomeClass atk') atk = atk'

{- for check-term and check-type, if the optional classifier is given, we will check against it.
   Otherwise, we will try to synthesize a type.  

   check-termi does not have to worry about normalizing the type it is given or the one it
   produces, nor about instantiating with the subject.  This will be handled by interleaved 
   calls to check-term.

   check-type should return kinds in hnf using check-type-return.

   Use add-tk above to add declarations to the ctxt, since these should be normalized
   and with self-types instantiated.
 -}
{-# NO_TERMINATION_CHECK #-}
check-term : ctxt → term → (m : maybe type) → spanM (check-ret m)
check-termi : ctxt → term → (m : maybe type) → spanM (check-ret m)
check-type : ctxt → type → (m : maybe kind) → spanM (check-ret m)
check-typei : ctxt → type → (m : maybe kind) → spanM (check-ret m)
check-kind : ctxt → kind → spanM ⊤
check-tk : ctxt → tk → spanM ⊤

check-term Γ subject nothing = check-termi Γ subject nothing
check-term Γ subject (just tp) = 
  check-termi Γ subject (just (if is-intro-form subject then (hnf-instantiate-iota Γ subject tp) else tp))

check-type Γ subject nothing = check-typei Γ subject nothing
check-type Γ subject (just k) = check-typei Γ subject (just (hnf Γ unfold-head k))

check-termi Γ (Parens pi t pi') tp = check-term Γ t tp
check-termi Γ (Var pi x) tp with ctxt-lookup-term-var Γ x
check-termi Γ (Var pi x) tp | nothing = 
  spanM-add (Var-span pi x 
              (error-data "Missing a type for a term variable." :: 
               expected-type-if tp (missing-type :: []))) ≫span
  return-when tp tp
check-termi Γ (Var pi x) nothing | just tp = 
  spanM-add (Var-span pi x ((type-data tp) :: [])) ≫span
  check-termi-return Γ (Var pi x) tp
check-termi Γ (Var pi x) (just tp) | just tp' = 
  spanM-add (Var-span pi x 
               (if conv-type Γ tp tp' then (expected-type tp :: [ type-data tp' ])
                 else (error-data "The computed type does not match the expected type." :: 
                       expected-type tp :: 
                       type-data tp' :: ("hnf expected" , type-to-string (hnf-term-type Γ unfold-head tp))
                       :: ("hnf computed" , type-to-string (hnf-term-type Γ unfold-head tp')) :: [])))

check-termi Γ (AppTp t tp') tp =
  check-term Γ t nothing ≫=spanm (λ htp → cont (hnf-instantiate-iota Γ t htp)) ≫=spanr cont' tp 
  where cont : type → spanM (maybe type)
        cont (Abs pi b pi' x (Tkk k) tp2) = 
           check-type Γ tp' (just k) ≫span 
           spanMr (just (subst-type Γ tp' x tp2))
        cont tp'' = spanM-add (AppTp-span t tp'
                               (error-data ("The type computed for the head of the application does"
                                        ^ " not allow the head to be applied to the (type) argument ")
                            :: term-app-head t
                            :: head-type tp'' 
                            :: type-argument tp'
                            :: [])) ≫span
                  spanMr nothing
        cont' : (outer : maybe type) → type → spanM (check-ret outer)
        cont' nothing tp'' = 
          spanM-add (AppTp-span t tp' ((type-data (hnf Γ unfold-head tp'')) :: [])) ≫span
          check-termi-return Γ (AppTp t tp') tp''
        cont' (just tp) tp'' = 
          if conv-type Γ tp tp'' then spanM-add (AppTp-span t tp' (expected-type tp :: [ type-data tp'' ]))
          else spanM-add (AppTp-span t tp' 
                           (error-data "The type computed for a term application does not match the expected type." ::
                            expected-type tp ::
                            type-data tp'' ::
                            []))
  
check-termi Γ (App t m t') tp =
  check-term Γ t nothing ≫=spanm (λ htp → cont m (hnf-instantiate-iota Γ t htp)) ≫=spanr cont' tp 
  where cont : maybeErased → type → spanM (maybe type)
        cont NotErased (TpArrow tp1 tp2) = 
          check-term Γ t' (just tp1) ≫span 
          check-termi-return Γ (App t m t') tp2
        cont Erased (TpArrow tp1 tp2) = 
          check-term-app-erased-error Erased t t' (TpArrow tp1 tp2)
        cont m (Abs pi b pi' x (Tkt tp1) tp2) = 
          if check-term-app-matching-erasures m b then
             (check-term Γ t' (just tp1) ≫span 
              check-termi-return Γ (App t m t') (subst-type Γ t' x tp2))
          else
            check-term-app-erased-error m t t' (Abs pi b pi' x (Tkt tp1) tp2)
        cont m tp' = spanM-add (App-span t t'
                               (error-data ("The type computed for the head of the application does"
                                        ^ " not allow the head to be applied to " ^ h m ^ " argument ")
                            :: term-app-head t
                            :: head-type tp' 
                            :: term-argument t'
                            :: [])) ≫span
                  spanMr nothing
                  where h : maybeErased → string
                        h Erased = "an erased term"
                        h NotErased = "a term"
        -- the type should already be normalized and instantiated
        cont' : (outer : maybe type) → type → spanM (check-ret outer)
        cont' nothing tp' = 
          spanM-add (App-span t t' [ type-data tp' ]) ≫span
          spanMr (just tp') -- already normalizedby cont
        cont' (just tp) tp' = 
          if conv-type Γ tp tp' then spanM-add (App-span t t' (expected-type tp :: type-data tp' :: []))
          else spanM-add (App-span t t' 
                           (error-data "The type computed for a term application does not match the expected type." ::
                            expected-type tp ::
                            type-data tp' :: 
                            hnf-expected-type-if Γ (just tp) []))
check-termi Γ (Lam pi l pi' x (SomeClass atk) t) nothing =
  check-tk Γ atk ≫span
  add-tk Γ pi x atk ≫=span λ Γ → 
  check-term Γ t nothing ≫=span cont

  where cont : maybe type → spanM (maybe type)
        cont nothing = spanM-add (Lam-span pi l x (SomeClass atk) t
                                    [ explain "Cannot compute a type because of errors in the body" ]) ≫span 
                       spanMr nothing
        cont (just tp) = 
          let rettp = abs-tk l x atk tp in
          spanM-add (Lam-span pi l x (SomeClass atk) t [ type-data rettp ]) ≫span
          check-termi-return Γ (Lam pi l pi' x (SomeClass atk) t) rettp

check-termi Γ (Lam pi l _ x NoClass t) nothing =
  spanM-add (Lam-span pi l x NoClass t [ error-data ("We are not checking this abstraction against a type, so a classifier must be"
                                                  ^ " given for the bound variable " ^ x) ]) ≫span
  spanMr nothing

check-termi Γ (Lam pi l pi' x oc t) (just tp) with to-abs tp 
check-termi Γ (Lam pi l pi' x oc t) (just tp) | just (mk-abs pi'' b pi''' x' atk _ tp') =
  spanM-add (this-span oc (check-erasures l b)) ≫span
  add-tk Γ pi' x (lambda-bound-class-if oc atk) ≫=span λ Γ → 
    check-term Γ t (just (rename-type Γ x' x (tk-is-type atk) tp'))

  where this-span : optClass → 𝕃 tagged-val → span
        this-span NoClass tvs = Lam-span pi l x oc t tvs
        this-span (SomeClass atk') tvs = 
          if conv-tk Γ atk' atk then
            Lam-span pi l x oc t tvs
          else
            Lam-span pi l x oc t (lambda-bound-var-conv-error x atk atk' tvs)
        check-erasures : lam → binder → 𝕃 tagged-val
        check-erasures ErasedLambda All = [ type-data tp ]
        check-erasures KeptLambda Pi = [ type-data tp ]
        check-erasures ErasedLambda Pi = error-data ("The expected type is a Π-abstraction (indicating explicit input), but"
                                              ^ " the term is a Λ-abstraction (implicit input).")
                                     :: [ expected-type tp ]
        check-erasures KeptLambda All = error-data ("The expected type is a ∀-abstraction (indicating implicit input), but"
                                              ^ " the term is a λ-abstraction (explicit input).")
                                     :: [ expected-type tp ]

check-termi Γ (Lam pi l _ x oc t) (just tp) | nothing =
  spanM-add (Lam-span pi l x oc t (error-data "The expected type is not of the form that can classify a λ-abstraction" ::
                                   expected-type tp :: []))

check-termi Γ (Beta pi) (just (TpEq t1 t2)) = 
  if conv-term Γ t1 t2 then
    spanM-add (Beta-span pi [ type-data (TpEq t1 t2) ])
  else
    spanM-add (Beta-span pi (error-data "The two terms in the equation are not β-equal" :: [ expected-type (TpEq t1 t2) ]))

check-termi Γ (Beta pi) nothing = 
  spanM-add (Beta-span pi [ error-data "An expected type is required in order to type a use of β." ]) ≫span spanMr nothing

check-termi Γ (Epsilon pi lr t) (just (TpEq t1 t2)) = 
  spanM-add (Epsilon-span pi lr t tt [ type-data (TpEq t1 t2) ]) ≫span
  check-term Γ t (just (check-term-update-eq Γ lr t1 t2))

check-termi Γ (Epsilon pi lr t) (just tp) = 
  spanM-add (Epsilon-span pi lr t tt (error-data ("The expected type is not an equation, when checking an ε-term.") 
                                 :: [ expected-type tp ])) ≫span 
  spanMok
check-termi Γ (Epsilon pi lr t) nothing = 
  check-term Γ t nothing ≫=span cont
  where cont : maybe type → spanM (maybe type)
        cont nothing = 
          spanM-add (Epsilon-span pi lr t ff [ error-data ("There is no expected type, and we could not synthesize a type from the body"
                                                      ^ " of the ε-term.") ]) ≫span
          spanMr nothing
        cont (just (TpEq t1 t2)) = 
          let r = check-term-update-eq Γ lr t1 t2 in
          spanM-add (Epsilon-span pi lr t ff [ type-data r ]) ≫span
          spanMr (just r)
        cont (just tp) = 
          spanM-add (Epsilon-span pi lr t ff ( error-data ("There is no expected type, and the type we synthesized for the body"
                                                      ^ " of the ε-term is not an equation.")
                                          :: ["the synthesized type" , type-to-string tp ])) ≫span
          spanMr nothing

check-termi Γ (Sigma pi t) mt = 
  check-term Γ t nothing ≫=span cont mt
  where cont : (outer : maybe type) → maybe type → spanM (check-ret outer)
        cont mt nothing = 
          spanM-add (Sigma-span pi t mt [ error-data ("We could not synthesize a type from the body"
                                                    ^ " of the ς-term.") ]) ≫span
          check-fail mt
        cont mt (just (TpEq t1 t2)) with TpEq t2 t1 
        cont nothing (just (TpEq t1 t2)) | r =
          spanM-add (Sigma-span pi t nothing [ type-data r ]) ≫span
          spanMr (just r)
        cont (just tp) (just (TpEq t1 t2)) | r =
          (if conv-type Γ tp r then
            spanM-add (Sigma-span pi t (just tp) [ type-data r ])
          else
            spanM-add (Sigma-span pi t (just tp) (error-data "The expected type does not match the computed type" :: [ type-data r ])))
          ≫span spanMok
        cont mt (just tp) = 
          spanM-add (Sigma-span pi t mt ( error-data ("The type we synthesized for the body"
                                                      ^ " of the ς-term is not an equation.")
                                          :: ["the synthesized type" , type-to-string tp ])) ≫span
          check-fail mt

check-termi Γ (Rho pi t t') (just tp) = 
  check-term Γ t nothing ≫=span cont
  where cont : maybe type → spanM ⊤
        cont nothing = spanM-add (Rho-span pi t t' tt [ expected-type tp ]) 
        cont (just (TpEq t1 t2)) = 
           check-term Γ t' (just (rewrite-type Γ empty-renamectxt t1 t2 tp)) ≫span
           spanM-add (Rho-span pi t t' tt ( ("the equation" , type-to-string (TpEq t1 t2)) :: [ type-data tp ]))
        cont (just tp') = spanM-add (Rho-span pi t t' tt
                                       (error-data "We could not synthesize an equation from the first subterm in a ρ-term."
                                     :: ("the synthesized type for the first subterm" , type-to-string tp')
                                     :: [ expected-type tp ])) 

check-termi Γ (Rho pi t t') nothing = 
  check-term Γ t nothing ≫=span λ mtp → 
  check-term Γ t' nothing ≫=span cont mtp
  where cont : maybe type → maybe type → spanM (maybe type)
        cont (just (TpEq t1 t2)) (just tp) = 
          let tp' = rewrite-type Γ empty-renamectxt t1 t2 tp in
            spanM-add (Rho-span pi t t' ff [ type-data tp' ]) ≫span
            check-termi-return Γ (Rho pi t t') tp'
        cont (just tp') m2 = spanM-add (Rho-span pi t t' ff
                                         (error-data "We could not synthesize an equation from the first subterm in a ρ-term."
                                      :: ("the synthesized type for the first subterm" , type-to-string tp')
                                      :: [])) ≫span spanMr nothing
        cont nothing _ = spanM-add (Rho-span pi t t' ff []) ≫span spanMr nothing

check-termi Γ (Theta pi u t ls) nothing =
  spanM-add (Theta-span pi u t ls [ error-data "Theta-terms can only be used in checking positions (and this is a synthesizing one)." ])
  ≫span spanMr nothing

check-termi Γ (Theta pi AbstractEq t ls) (just tp) =
  -- discard spans from checking t, because we will check it again below
  check-term Γ t nothing ≫=spand 
    (λ htp → let x = (fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt) in
                 cont (mtplam x (Tkt htp) (TpArrow (TpEq t (mvar x)) tp)))
  where cont : type → spanM ⊤
        cont motive = spanM-add (Theta-span pi AbstractEq t ls [ the-motive motive ]) ≫span 
                      check-term Γ (App* (AppTp t (NoSpans motive (posinfo-plus (term-end-pos t) 1)))
                                         (lterms-to-𝕃 AbstractEq ls)) (just tp)

check-termi Γ (Theta pi Abstract (Var pi' x) ls) (just tp) =
  -- discard spans from checking the head, because we will check it again below
  check-term Γ (Var pi' x) nothing ≫=spand (λ htp → cont (mtplam x (Tkt htp) tp))
  where cont : type → spanM ⊤
        cont motive = spanM-add (Theta-span pi Abstract (Var pi' x) ls [ the-motive motive ]) ≫span 
                      check-term Γ (App* (AppTp (Var pi' x) (NoSpans motive (posinfo-plus pi' (suc (string-length x)))))
                                   (lterms-to-𝕃 Abstract ls)) (just tp)

check-termi Γ (Theta pi Abstract t ls) (just tp) =
  spanM-add (Theta-span pi Abstract t ls [ error-data "Abstracting a non-variable term is not implemented yet." ])
  ≫span spanMr triv

check-termi Γ (Hole pi) tp = spanM-add (hole-span Γ pi tp [ local-ctxt-data Γ ]) ≫span return-when tp tp

check-termi Γ t tp = spanM-add (unimplemented-term-span (term-start-pos t) (term-end-pos t) tp) ≫span unimplemented-if tp

check-typei Γ (TpParens pi t pi') k = check-type Γ t k
check-typei Γ (NoSpans t _) k ss = fst (check-type Γ t k ss) , ss
check-typei Γ (TpVar pi x) k with ctxt-lookup-type-var Γ x
check-typei Γ (TpVar pi x) k | nothing = 
  spanM-add (TpVar-span pi x 
              (error-data "Missing a kind for a type variable." :: 
               expected-kind-if k (missing-kind :: []))) ≫span
  return-when k k
check-typei Γ (TpVar pi x) nothing | (just k) = 
  spanM-add (TpVar-span pi x ((kind-data k) :: [])) ≫span
  check-type-return Γ k
check-typei Γ (TpVar pi x) (just k) | just k' = 
  if conv-kind Γ k k' 
  then spanM-add (TpVar-span pi x 
                    (expected-kind k :: [ kind-data k' ]))
  else spanM-add (TpVar-span pi x 
                   (error-data "The computed kind does not match the expected kind." :: 
                    expected-kind k ::
                    [ kind-data k' ]))
check-typei Γ (TpLambda pi pi' x atk' body) (just k) with to-absk k
check-typei Γ (TpLambda pi pi' x atk body) (just k) | just (mk-absk pik pik' x' atk' _ k') =
  check-tk Γ atk ≫span
  spanM-add (if conv-tk Γ atk atk' then
               TpLambda-span pi x atk body [ kind-data k ]
             else
               TpLambda-span pi x atk body (lambda-bound-var-conv-error x atk' atk [ kind-data k ])) ≫span
  add-tk Γ pi' x atk ≫=span λ Γ → 
    check-type Γ body (just (rename-kind Γ x' x (tk-is-type atk') k'))
          
check-typei Γ (TpLambda pi pi' x atk body) (just k) | nothing =
  check-tk Γ atk ≫span
  spanM-add (TpLambda-span pi x atk body
               (error-data "The type is being checked against a kind which is not an arrow- or Pi-kind." ::
                expected-kind k :: []))

check-typei Γ (TpLambda pi pi' x atk body) nothing =
  check-tk Γ atk ≫span
  add-tk Γ pi' x atk ≫=span λ Γ → 
  check-type Γ body nothing ≫=span cont

  where cont : maybe kind → spanM (maybe kind)
        cont nothing = 
          spanM-add (TpLambda-span pi x atk body []) ≫span spanMr nothing
        cont (just k) = 
          let r = absk-tk x atk k in
            spanM-add (TpLambda-span pi x atk body [ kind-data r ]) ≫span 
            spanMr (just r)

check-typei Γ (Abs pi b {- All or Pi -} pi' x atk body) k = 
  spanM-add (TpQuant-span (binder-is-pi b) pi x atk body (if-check-against-star-data "A type-level quantification" k)) ≫span
  check-tk Γ atk ≫span
  add-tk Γ pi' x atk ≫=span λ Γ → 
  check-type Γ body (just star) ≫span
  return-star-when k
  where helper : maybe kind → 𝕃 tagged-val
        helper nothing = [ kind-data star ]
        helper (just (Star _)) = [ kind-data star ]
        helper (just k) = error-data "A type-level quantification is being checked against a kind other than ★" ::
                          expected-kind k :: []

check-typei Γ (TpArrow t1 t2) k = 
  spanM-add (TpArrow-span t1 t2 (if-check-against-star-data "An arrow type" k)) ≫span
  check-type Γ t1 (just star) ≫span
  check-type Γ t2 (just star) ≫span
    return-star-when k

check-typei Γ (TpAppt tp t) k =
  check-type Γ tp nothing ≫=spanm cont ≫=spanr cont' k
  where cont : kind → spanM (maybe kind)
        cont (KndTpArrow tp' k') = 
          check-term Γ t (just tp') ≫span 
          spanMr (just k')
        cont (KndPi _ _ x (Tkt tp') k') = 
          check-term Γ t (just tp') ≫span 
          spanMr (just (subst-kind Γ t x k'))
        cont k' = spanM-add (TpAppt-span tp t
                               (error-data ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a term")
                            :: type-app-head tp
                            :: head-kind k' 
                            :: term-argument t
                            :: [])) ≫span
                  spanMr nothing
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          spanM-add (TpAppt-span tp t ((kind-data k) :: [])) ≫span
          check-type-return Γ k
        cont' (just k') k = 
          if conv-kind Γ k k' then spanM-add (TpAppt-span tp t (expected-kind k' :: [ kind-data k ]))
          else spanM-add (TpAppt-span tp t 
                           (error-data "The kind computed for a type application does not match the expected kind." ::
                            expected-kind k' ::
                            kind-data k ::
                            []))

check-typei Γ (TpApp tp tp') k =
  check-type Γ tp nothing ≫=spanm cont ≫=spanr cont' k
  where cont : kind → spanM (maybe kind)
        cont (KndArrow k'' k') = 
          check-type Γ tp' (just k'') ≫span 
          spanMr (just k')
        cont (KndPi _ _ x (Tkk k'') k') = 
          check-type Γ tp' (just k'') ≫span 
          spanMr (just (subst-kind Γ tp' x k'))
        cont k' = spanM-add (TpApp-span tp tp'
                               (error-data ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a type")
                            :: type-app-head tp
                            :: head-kind k' 
                            :: type-argument tp'
                            :: [])) ≫span
                  spanMr nothing
        cont' : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont' nothing k = 
          spanM-add (TpApp-span tp tp' ((kind-data k) :: [])) ≫span
          check-type-return Γ k
        cont' (just k') k = 
          if conv-kind Γ k k' then spanM-add (TpApp-span tp tp' (expected-kind k' :: [ kind-data k' ]))
          else spanM-add (TpApp-span tp tp' 
                           (error-data "The kind computed for a type application does not match the expected kind." ::
                            expected-kind k' ::
                            kind-data k ::
                            []))

check-typei Γ (TpEq t1 t2) k = 
  spanM-add (TpEq-span t1 t2 (if-check-against-star-data "An equation" k)) ≫span
  return-star-when k
  
check-typei Γ (Lft pi pi' X t l) k = 
  add-tk Γ pi' X (Tkk star) ≫=span λ Γ →
  check-term Γ t (just (liftingType-to-type X l)) ≫span
  cont k (liftingType-to-kind l) 
  where cont : (outer : maybe kind) → kind → spanM (check-ret outer)
        cont nothing k = spanM-add (Lft-span pi X t l [ kind-data k ]) ≫span spanMr (just k)
        cont (just k') k = 
          if conv-kind Γ k k' then 
             spanM-add (Lft-span pi X t l ( expected-kind k' :: [ kind-data k ])) ≫span spanMok
          else
             spanM-add (Lft-span pi X t l ( error-data "The expected kind does not match the computed kind."
                                         :: expected-kind k' :: [ kind-data k ]))
check-typei Γ t k = spanM-add (unimplemented-type-span (type-start-pos t) (type-end-pos t) k) ≫span unimplemented-if k

check-kind Γ (KndParens _ k _) = check-kind Γ k
check-kind Γ (Star pi) = spanM-add (Star-span pi)
check-kind Γ (KndVar pi x) = spanM-add (KndVar-span pi x)
check-kind Γ (KndArrow k k') = 
  spanM-add (KndArrow-span k k') ≫span
  check-kind Γ k ≫span
  check-kind Γ k'
check-kind Γ (KndTpArrow t k) = 
  spanM-add (KndTpArrow-span t k) ≫span
  check-type Γ t (just star) ≫span
  check-kind Γ k
check-kind Γ (KndPi pi pi' x atk k) = 
  spanM-add (KndPi-span pi x atk k) ≫span
  check-tk Γ atk ≫span
  add-tk Γ pi' x atk ≫=span λ Γ → 
  check-kind Γ k

check-tk Γ (Tkk k) = check-kind Γ k
check-tk Γ (Tkt t) = check-type Γ t (just star)


