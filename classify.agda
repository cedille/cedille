module classify where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import hnf
open import is-free
open import rename
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

-- return a kind in hnf
check-type-return : ctxt → kind → spanM (maybe kind)
check-type-return Γ k = spanMr (just (hnf Γ tt k))

{- if the hnf of the type is a Iota type, then instantiate it with the given term.
   We assume types do not reduce with normalization and instantiation to further iota
   types. -}
hnf-instantiate-iota : ctxt → term → type → type
hnf-instantiate-iota Γ subject tp with hnf Γ tt tp
hnf-instantiate-iota Γ subject _ | Iota _ x t = hnf Γ tt (subst-type Γ subject x t)
hnf-instantiate-iota Γ subject _ | tp = tp

add-tk : ctxt → posinfo → var → tk → spanM ctxt
add-tk Γ pi x atk =
  spanM-add (var-span pi x atk) ≫span
  spanMr (helper atk)
  where helper : tk → ctxt
        helper (Tkk k) = ctxt-type-decl x (hnf Γ tt k) Γ
        helper (Tkt t) = ctxt-term-decl x (hnf-instantiate-iota Γ (Var posinfo-gen x) t) Γ

{- for check-term and check-type, if the optional classifier is given, we will check against it.
   Otherwise, we will try to synthesize a type.  

   check-termi does not have to worry about normalizing the type it is given or the one it
   produces, nor about instantiating with the subject.  This will be handled by interleaved 
   calls to check-term.

   check-type should return kinds in hnf using check-type-return.

   Use add-tk above to add declarations to the ctxt, since these should be normalized
   and with self-types instantiated.
 -}
check-term : ctxt → term → (m : maybe type) → spanM (check-ret m)
check-termi : ctxt → term → (m : maybe type) → spanM (check-ret m)
check-type : ctxt → type → (m : maybe kind) → spanM (check-ret m)
check-kind : ctxt → kind → spanM ⊤
check-tk : ctxt → tk → spanM ⊤

-- call hnf-instantiate-iota on types coming in or going out of check-termi
check-term Γ subject nothing =
  check-termi Γ subject nothing ≫=spanm λ tp → spanMr (just (hnf-instantiate-iota Γ subject tp))
check-term Γ subject (just tp) =
  let tp' = hnf-instantiate-iota Γ subject tp in
    spanM-debug (term-start-pos subject) (term-end-pos subject)
                 (("type coming in to check-term" , type-to-string tp) ::
                  ("type being forwarded along to check-termi" , type-to-string tp') :: []) ≫span
    check-termi Γ subject (just tp')

check-termi Γ (Parens pi t pi') tp = check-term Γ t tp
check-termi Γ (Var pi x) tp with ctxt-lookup-term-var Γ x
check-termi Γ (Var pi x) tp | nothing = 
  spanM-add (Var-span pi x 
              (error-data "Missing a type for a term variable." :: 
               expected-type-if tp (missing-type :: []))) ≫span
  return-when tp tp
check-termi Γ (Var pi x) nothing | just tp = 
  spanM-add (Var-span pi x ((type-data tp) :: [])) ≫span
  spanMr (just tp)
check-termi Γ (Var pi x) (just tp) | just tp' = 
  spanM-add (Var-span pi x 
               (type-data tp' ::
                (if conv-type Γ tp (hnf-instantiate-iota Γ (Var pi x) tp') then []
                 else (error-data "The computed type does not match the expected type." :: 
                       expected-type tp :: 
                       [ ctxt-data Γ ]))))
check-termi Γ (AppTp t tp') tp =
  check-term Γ t nothing ≫=spanm cont ≫=spanr cont' tp 
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
          spanM-add (AppTp-span t tp' ((type-data tp'') :: [])) ≫span
          spanMr (just tp'')
        cont' (just tp) tp'' = 
          if conv-type Γ tp tp'' then spanM-add (AppTp-span t tp' ((type-data tp'') :: []))
          else spanM-add (AppTp-span t tp' 
                           (error-data "The type computed for a term application does not match the expected type." ::
                            expected-type tp ::
                            type-data tp'' ::
                            []))
  
check-termi Γ (App t m t') tp =
  check-term Γ t nothing ≫=spanm cont m ≫=spanr cont' tp 
  where instr : type → spanM (maybe type)
        instr tp = spanMr (just (hnf-instantiate-iota Γ (App t m t') tp))

        cont : maybeErased → type → spanM (maybe type)
        cont NotErased (TpArrow tp1 tp2) = 
          check-term Γ t' (just tp1) ≫span 
          instr tp2
        cont Erased (TpArrow tp1 tp2) = 
          check-term-app-erased-error Erased t t' (TpArrow tp1 tp2)
        cont m (Abs pi b pi' x (Tkt tp1) tp2) = 
          if check-term-app-matching-erasures m b then
             (check-term Γ t' (just tp1) ≫span 
              instr (subst-type Γ t' x tp2))
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
        cont' : (outer : maybe type) → type → spanM (check-ret outer)
        cont' nothing tp' = 
          spanM-add (App-span t t' [ type-data tp' ]) ≫span
          spanMr (just tp')
        cont' (just tp) tp' = 
          if conv-type Γ tp tp' then spanM-add (App-span t t' (expected-type tp :: type-data tp' :: []))
          else spanM-add (App-span t t' 
                           (error-data "The type computed for a term application does not match the expected type." ::
                            expected-type tp ::
                            type-data tp' ::
                            [ ctxt-data Γ ]))
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
           spanMr (just rettp)

check-termi Γ (Lam pi l _ x NoClass t) nothing =
  spanM-add (Lam-span pi l x NoClass t [ error-data ("We are not checking this abstraction against a type, so a classifier must be"
                                                  ^ " given for the bound variable " ^ x) ]) ≫span
  spanMr nothing

check-termi Γ (Lam pi l pi' x oc t) (just tp) with to-abs tp 
check-termi Γ (Lam pi l pi' x oc t) (just tp) | just (mk-abs pi'' b pi''' x' atk _ tp') =
  spanM-add (this-span oc (check-erasures l b)) ≫span
  add-tk Γ pi' x atk ≫=span λ Γ → 
  let Γ = ctxt-rename x' x Γ in
    check-term Γ t (just tp')

  where this-span : optClass → 𝕃 tagged-val → span
        this-span NoClass tvs = Lam-span pi l x oc t tvs
        this-span (SomeClass atk') tvs = 
          if conv-tk Γ atk' atk then
            Lam-span pi l x oc t tvs
          else
            Lam-span pi l x oc t (( error-data "The classifier given for a λ-bound variable is not the one we expected"
                                :: ("the variable" , x)
                                :: ("its declared classifier" , tk-to-string atk')
                                :: [ "the expected classifier" , tk-to-string atk ]) ++ tvs)
        check-erasures : lam → binder → 𝕃 tagged-val
        check-erasures ErasedLambda All = [ expected-type tp ]
        check-erasures KeptLambda Pi = [ expected-type tp ]
        check-erasures ErasedLambda Pi = error-data ("The expected type is a Π-abstraction (indicating explicit input), but"
                                              ^ " the term is a Λ-abstraction (implicit input).")
                                     :: [ expected-type tp ]
        check-erasures KeptLambda All = error-data ("The expected type is a ∀-abstraction (indicating implicit input), but"
                                              ^ " the term is a λ-abstraction (explicit input).")
                                     :: [ expected-type tp ]
        check-erasures _ TpLambda = error-data ("The expected type is a type-level λ-abstraction, which cannot classify"
                                              ^ " a term-level λ-abstraction.")
                                :: [ expected-type tp ]

check-termi Γ (Lam pi l _ x oc t) (just tp) | nothing =
  spanM-add (Lam-span pi l x oc t (error-data "The expected type is not of the form that can classify a λ-abstraction" ::
                                   expected-type tp :: []))

check-termi Γ t tp = unimplemented-if tp

check-type Γ tp (just (KndParens _ k _)) = check-type Γ tp (just k)
check-type Γ (TpParens pi t pi') k = check-type Γ t k
check-type Γ (TpVar pi x) k with ctxt-lookup-type-var Γ x
check-type Γ (TpVar pi x) k | nothing = 
  spanM-add (TpVar-span pi x 
              (error-data "Missing a kind for a type variable." :: 
               expected-kind-if k (missing-kind :: []))) ≫span
  return-when k k
check-type Γ (TpVar pi x) nothing | (just k) = 
  spanM-add (TpVar-span pi x ((kind-data k) :: [])) ≫span
  check-type-return Γ k
check-type Γ (TpVar pi x) (just k) | just k' = 
  if conv-kind Γ k k' 
  then spanM-add (TpVar-span pi x 
                    ((kind-data k') :: []))
  else spanM-add (TpVar-span pi x 
                   (error-data "The computed kind does not match the expected kind." :: 
                    expected-kind k ::
                    kind-data k' :: []))
check-type Γ (Abs pi TpLambda pi' x atk body) (just (KndArrow k1 k2)) = unimplemented-check
check-type Γ (Abs pi TpLambda pi' x atk body) (just (KndTpArrow k1 k2)) = unimplemented-check
check-type Γ (Abs pi TpLambda pi' x atk body) (just (KndPi _ _ x' atk' k)) = unimplemented-check
check-type Γ (Abs pi TpLambda pi' x atk body) (just k) = 
  spanM-add (TpLambda-span pi x atk body
               (error-data "The type is being checked against a kind which is not an arrow- or Pi-kind." ::
                expected-kind k :: []))

check-type Γ (Abs pi b {- All or Pi -} pi' x atk body) k = 
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

check-type Γ (TpArrow t1 t2) k = 
  spanM-add (TpArrow-span t1 t2 (if-check-against-star-data "An arrow type" k)) ≫span
  check-type Γ t1 (just star) ≫span
  check-type Γ t2 (just star) ≫span
    return-star-when k

check-type Γ (TpAppt tp t) k =
  check-type Γ tp nothing ≫=spanm cont ≫=spanr cont' k
  where cont : kind → spanM (maybe kind)
        cont (KndTpArrow tp' k') = 
          check-term Γ t (just tp') ≫span 
          spanMr (just k')
        cont (KndPi _ _ x (Tkk k1) k') = unimplemented-synth
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
          if conv-kind Γ k k' then spanM-add (TpAppt-span tp t ((kind-data k') :: []))
          else spanM-add (TpAppt-span tp t 
                           (error-data "The kind computed for a type application does not match the expected kind." ::
                            expected-kind k' ::
                            kind-data k ::
                            []))
  
check-type Γ t k = unimplemented-if k

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


