module classify where

open import lib

open import cedille-types
open import conversion
open import ctxt
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


{- for check-term and check-type, if the optional classifier is given, we will check against it.
   Otherwise, we will try to synthesize a type -}
check-term : ctxt → term → (m : maybe type) → spanM (check-ret m)
check-type : ctxt → type → (m : maybe kind) → spanM (check-ret m)
check-kind : ctxt → kind → spanM ⊤
check-tk : ctxt → tk → spanM ⊤

check-term Γ (Parens pi t pi') tp = 
  spanM-add (parens-span pi pi') ≫span
  check-term Γ t tp
check-term Γ (Var pi x) tp with ctxt-lookup-term-var Γ x
check-term Γ (Var pi x) tp | nothing = 
  spanM-add (Var-span pi x 
              (error-data "Missing a type for a term variable." :: 
               expected-type-if tp (missing-type :: []))) ≫span
  return-when tp tp
check-term Γ (Var pi x) nothing | just tp = 
  spanM-add (Var-span pi x ((type-data tp) :: [])) ≫span
  spanMr (just tp)
check-term Γ (Var pi x) (just tp) | just tp' = 
  spanM-add (Var-span pi x 
               (type-data tp' ::
                (if conv-type Γ tp tp' then []
                 else (error-data "The computed type does not match the expected type." :: 
                       expected-type tp :: []))))
check-term Γ t tp = unimplemented-if tp

check-type Γ tp (just (KndParens _ k _)) = check-type Γ tp (just k)
check-type Γ (TpParens pi t pi') k = 
  spanM-add (parens-span pi pi') ≫span check-type Γ t k
check-type Γ (TpVar pi x) k with ctxt-lookup-type-var Γ x
check-type Γ (TpVar pi x) k | nothing = 
  spanM-add (TpVar-span pi x 
              (error-data "Missing a kind for a type variable." :: 
               expected-kind-if k (missing-kind :: []))) ≫span
  return-when k k
check-type Γ (TpVar pi x) nothing | (just k) = 
  spanM-add (TpVar-span pi x ((kind-data k) :: [])) ≫span
  spanMr (just k)
check-type Γ (TpVar pi x) (just k) | just k' = 
  if conv-kind Γ k k' 
  then spanM-add (TpVar-span pi x 
                    ((kind-data k') :: []))
  else spanM-add (TpVar-span pi x 
                   (error-data "The computed kind does not match the expected kind." :: 
                    expected-kind k ::
                    kind-data k' ::
                    []))
check-type Γ (Abs pi TpLambda x atk body) (just (KndArrow k1 k2)) = unimplemented-check
check-type Γ (Abs pi TpLambda x atk body) (just (KndTpArrow k1 k2)) = unimplemented-check
check-type Γ (Abs pi TpLambda x atk body) (just (KndPi _ x' atk' k)) = unimplemented-check
check-type Γ (Abs pi TpLambda x atk body) (just k) = 
  spanM-add (TpLambda-span pi x atk body
               (error-data "The type is being checked against a kind which is not an arrow- or Pi-kind." ::
                expected-kind k :: []))

check-type Γ (Abs pi b {- All or Pi -} x atk body) k = 
  spanM-add (TpQuant-span (binder-is-pi b) pi x atk body (if-check-against-star-data "A type-level quantification" k)) ≫span
  check-tk Γ atk ≫span
  check-type (ctxt-tk-decl x atk Γ) body (just star) ≫span
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
        cont (KndParens _ k _) = cont k
        cont (KndTpArrow tp' k') = 
          check-term Γ t (just tp') ≫span 
          spanMr (just k')
        cont (KndPi _ x (Tkk k1) k') = unimplemented-synth
        cont (KndPi _ x (Tkt tp') k') = 
          let k'' = subst-kind Γ empty-renamectxt t x k' in
          check-term Γ t (just tp') ≫span 
          spanMr (just k'')
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
          spanMr (just k)
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
check-kind Γ (KndPi pi x atk k) = 
  spanM-add (KndPi-span pi x atk k) ≫span
  check-tk Γ atk ≫span
  check-kind (ctxt-tk-decl x atk Γ) k

check-tk Γ (Tkk k) = check-kind Γ k
check-tk Γ (Tkt t) = check-type Γ t (just star)


