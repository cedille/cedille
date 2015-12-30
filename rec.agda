{- code for checking recursive type definitions. -}
module rec where

open import lib

open import cedille-types
open import classify
open import ctxt
open import spans
open import syntax-util

{- check the given declaration, and return a new context binding the name in the declaration.

   The boolean tells if this is a parameter (tt) or an index (ff). -}
rec-check-and-add-decl : decl-class → ctxt → decl → spanM ctxt
rec-check-and-add-decl dc Γ (Decl pi x atk pi') = 
  check-tk Γ atk ≫span 
  spanM-add (Decl-span dc pi x atk pi') ≫span
  spanMr (ctxt-tk-decl Γ x atk)

{- check-and-add and add the given decls, returning an updated context.  The boolean tells if this
   is a parameter compute the kind for a recursive type from the given decls -}
rec-check-and-add-decls : decl-class → ctxt → decls → spanM ctxt
rec-check-and-add-decls dc Γ (DeclsCons d ds)  = 
  rec-check-and-add-decl dc Γ d ≫=span λ Γ → rec-check-and-add-decls dc Γ ds 
rec-check-and-add-decls dc Γ DeclsNil = spanMr Γ

rec-check-and-add-ctors : ctxt → ctxt → ctordecls → spanM ctxt
rec-check-and-add-ctors Γ Γ' x = spanMr Γ'

process-rec-cmd : ctxt → posinfo → var → decls → indices → ctordecls → type → udefs → posinfo → spanM ctxt
process-rec-cmd Γ pi name params inds ctors body us pi' = 
  let inds = indices-to-decls inds in
  rec-check-and-add-decls param Γ params ≫=span λ Γp → 

  -- check the indices in the ctxt containing the params
  rec-check-and-add-decls index Γp inds ≫=span λ Γpi → 

    let k = decls-pi-bind-kind params (Star posinfo-gen) in 
    let Γpt = ctxt-type-decl Γp name k in

      {- check the ctors in the ctxt containing just the params and the recursive type itself,
         adding the new definitions to the context containing the params and the indices -}
      rec-check-and-add-ctors Γpt Γpi ctors ≫=span λ Γpic →

      let Γpict = ctxt-type-decl Γpic name k in

      let k = decls-pi-bind-kind params (decls-pi-bind-kind inds (Star posinfo-gen)) in

        spanM-add (mk-span Rec-name pi pi' (Rec-explain name :: kind-data k :: [])) ≫span 
        spanMr (ctxt-rec-def Γ name body k)

{-  let inds = indices-to-decls inds in
  let p = (rec-compute-kind Γ params inds ≫=span λ k → 
          
          spanMr k) ss
  in
  let k = fst p in
  let ss' = snd p in
  let extra = params ++decls inds in
  let body' = decls-lambda-bind-kind extra body in
-}

