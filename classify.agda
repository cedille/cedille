module classify where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import spans
open import syntax-util

unimplemented : spanM ⊤
unimplemented = spanMr triv

check-type : ctxt → type → kind → spanM ⊤
check-kind : ctxt → kind → spanM ⊤
check-tk : ctxt → tk → spanM ⊤

check-kind Γ (Star pi) = spanM-add (mk-span Star-name pi (ℕ-to-string (suc (posinfo-to-ℕ pi))) [])
check-kind Γ k = unimplemented
check-type Γ (TpVar pi x) k with ctxt-lookup-kind Γ x
check-type Γ (TpVar pi x) k | nothing = spanM-add (TpVar-span x pi 
                                                     ((expected-kind k) ::
                                                       missing-kind ::
                                                       error-data "Missing a kind for a type variable." :: []))
check-type Γ (TpVar pi x) k | just k' = if conv-kind Γ k k' 
                                        then spanM-add (TpVar-span x pi 
                                                         ((kind-data k') :: []))
                                        else spanM-add (TpVar-span x pi 
                                                         ((expected-kind k) ::
                                                          (kind-data k') ::
                                                          error-data "The computed kind does not match the expected kind." :: []))
check-type Γ t k = unimplemented

check-tk Γ (Tkk k) = check-kind Γ k
check-tk Γ (Tkt t) = check-type Γ t (Star posinfo-gen)



