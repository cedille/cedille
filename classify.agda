module classify where

open import lib

open import cedille-types
open import conversion
open import ctxt
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

return-star-if : (m : maybe kind) → spanM (check-ret m)
return-star-if nothing = spanMr (just star)
return-star-if (just _) = spanMr triv

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

check-term Γ t tp = unimplemented-if tp

check-type Γ tp (just (KndParens _ k _)) = check-type Γ tp (just k)
check-type Γ (TpParens pi t pi') k = 
  spanM-add (parens-span pi pi') ≫span check-type Γ t k
check-type Γ (TpVar pi x) nothing with ctxt-lookup-kind Γ x
check-type Γ (TpVar pi x) nothing | nothing = 
  spanM-add (TpVar-span x pi 
              (error-data "Missing a kind for a type variable." :: 
               missing-kind :: [])) ≫span
  spanMr nothing
check-type Γ (TpVar pi x) nothing | (just k) = 
  spanM-add (TpVar-span x pi ((kind-data k) :: [])) ≫span
  spanMr (just k)
check-type Γ (TpVar pi x) (just k) with ctxt-lookup-kind Γ x
check-type Γ (TpVar pi x) (just k) | nothing =
  spanM-add (TpVar-span x pi 
              (error-data "Missing a kind for a type variable." ::
              expected-kind k ::
              missing-kind ::
              []))
check-type Γ (TpVar pi x) (just k) | just k' = 
  if conv-kind Γ k k' 
  then spanM-add (TpVar-span x pi 
                    ((kind-data k') :: []))
  else spanM-add (TpVar-span x pi 
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
  return-star-if k
  where helper : maybe kind → 𝕃 tagged-val
        helper nothing = [ kind-data star ]
        helper (just (Star _)) = [ kind-data star ]
        helper (just k) = error-data "A type-level quantification is being checked against a kind other than ★" ::
                          expected-kind k :: []

check-type Γ (TpArrow t1 t2) k = 
  spanM-add (TpArrow-span t1 t2 (if-check-against-star-data "An arrow type" k)) ≫span
  check-type Γ t1 (just star) ≫span
  check-type Γ t2 (just star) ≫span
    return-star-if k

check-type Γ (TpAppt tp t) k =
  check-type Γ tp nothing ≫=spanm cont ≫=spanr cont' k
  where cont : kind → spanM (maybe kind)
        cont (KndParens _ k _) = cont k
        cont (KndTpArrow tp' k') = 
          check-term Γ t (just tp') ≫span 
          spanM-add (TpAppt-span tp t [ kind-data k' ]) ≫span
          spanMr (just k')
        cont (KndPi _ x (Tkk k1) k') = unimplemented-synth
        cont (KndPi _ x (Tkt tp') k') = 
          let k'' = term-subst-kind Γ t x k' in
          check-term Γ t (just tp') ≫span 
          spanM-add (TpAppt-span tp t [ kind-data k'' ]) ≫span
          spanMr (just k'')
        cont k' = spanM-add (TpAppt-span tp t
                               (error-data ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a term")
                            :: type-app-head tp
                            :: head-kind k' 
                            :: term-argument t
                            :: [])) ≫span
                  spanMr nothing

        cont' : (m : maybe kind) → kind → spanM (check-ret m)
        cont' nothing k = spanMr (just k)
        cont' (just k') k = 
          if conv-kind Γ k k' then spanM-add (TpAppt-span tp t ((kind-data k') :: []))
          else spanM-add (TpAppt-span tp t 
                           (error-data "The kind computed for a type application does not match the expected kind." ::
                            expected-kind k' ::
                            kind-data k ::
                            []))
  
check-type Γ t k = unimplemented-if k

check-kind Γ (Star pi) = spanM-add (mk-span Star-name pi (posinfo-plus pi 1) [])
check-kind Γ k = unimplemented-check

check-tk Γ (Tkk k) = check-kind Γ k
check-tk Γ (Tkt t) = check-type Γ t (just star)


