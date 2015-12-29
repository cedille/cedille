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

{- check the given declaration, and return a new context (binding the name in the declaration),
   as well as a function that will wrap a Pi-binding for the declaration around a given kind.

   The boolean tells if this is a parameter (tt) or an index (ff). -}
rec-check-decl : 𝔹 → ctxt → decl → spanM (ctxt × (kind → kind))
rec-check-decl is-param Γ (Decl pi x atk pi') = 
  check-tk Γ atk ≫span 
  spanM-add (Decl-span is-param pi x atk pi') ≫span 
  spanMr (ctxt-tk-decl Γ x atk , KndPi x atk) 

{- compute the kind for a recursive type from the parameters (decls) and the indices -}
rec-compute-kind : ctxt → decls → indices → spanM kind
rec-compute-kind Γ (DeclsCons d ds) is = 
  rec-check-decl tt Γ d ≫=span λ p →  
    rec-compute-kind (fst p) ds is ≫=span λ k → spanMr (snd p k)
rec-compute-kind Γ DeclsNil Indicese = spanMr (Star posinfo-gen)
rec-compute-kind Γ DeclsNil (Indicesne (DeclsCons d ds)) = 
  rec-check-decl ff Γ d ≫=span λ p →  
    rec-compute-kind (fst p) DeclsNil (Indicesne ds) ≫=span λ k → spanMr (snd p k)
rec-compute-kind Γ DeclsNil (Indicesne DeclsNil) = spanMr (Star posinfo-gen)


