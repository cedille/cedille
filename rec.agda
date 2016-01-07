{- code for checking recursive type definitions. -}
module rec where

open import lib

open import cedille-types
open import classify
open import constants
open import ctxt
open import is-free
open import spans
open import subst
open import syntax-util

decls-pi-bind-kind : decls → kind → kind
decls-pi-bind-kind (DeclsNil _) k = k
decls-pi-bind-kind (DeclsCons (Decl _ x atk _) ds) k = 
  let k' = decls-pi-bind-kind ds k in
    if (is-free-in-kind check-erased x k') then
      KndPi posinfo-gen x atk k'
    else
      tk-arrow-kind atk k'

{- check the given declaration, and return a new context binding the name in the declaration.

   The boolean tells if this is a parameter (tt) or an index (ff). -}
rec-check-and-add-decl : decl-class → ctxt → decl → spanM ctxt
rec-check-and-add-decl dc Γ (Decl pi x atk pi') = 
  check-tk Γ atk ≫span 
  spanM-add (Decl-span dc pi x atk pi') ≫span
  spanMr (ctxt-tk-decl x atk Γ)

{- check-and-add and add the given decls, returning an updated context.  The boolean tells if this
   is a parameter compute the kind for a recursive type from the given decls -}
rec-check-and-add-decls : decl-class → ctxt → decls → spanM ctxt
rec-check-and-add-decls dc Γ (DeclsCons d ds)  = 
  rec-check-and-add-decl dc Γ d ≫=span λ Γ → rec-check-and-add-decls dc Γ ds 
rec-check-and-add-decls dc Γ (DeclsNil _) = spanMr Γ

{- check that the type in the ctordecl can be kinded with kind star,
   and then add a declaration for it to the ctxt. Spans will be added later -}
rec-check-and-add-ctor : ctxt → ctxt → ctordecl → spanM ctxt
rec-check-and-add-ctor Γ Γ' (Ctordecl pi x tp) = 
  check-type Γ tp (just star) ≫span
  spanMr (ctxt-term-decl x tp Γ')

{- check the types of all the ctors with respect to the first ctxt and
   then add declarations for them to the second ctxt.  -}
rec-check-and-add-ctors : ctxt → ctxt → ctordecls → spanM ctxt
rec-check-and-add-ctors Γ Γ' (Ctordeclse _) = spanMr Γ'
rec-check-and-add-ctors Γ Γ' (Ctordeclsne (CtordeclsneNext c cs)) = 
  rec-check-and-add-ctor Γ Γ' c ≫=span λ Γ' → rec-check-and-add-ctors Γ Γ' (Ctordeclsne cs)
rec-check-and-add-ctors Γ Γ' (Ctordeclsne (CtordeclsneStart c)) = rec-check-and-add-ctor Γ Γ' c

rec-apply-decls : type → decls → type
rec-apply-decls tp (DeclsNil _) = tp
rec-apply-decls tp (DeclsCons (Decl _ x atk _) ds) = rec-apply-decls (TpApp-tk tp x atk) ds

check-params-not-free : decls → term → spanM ⊤
check-params-not-free (DeclsCons (Decl pi x atk pi') params) t = 
  let r = check-params-not-free params t in
  if is-free-in-term skip-erased x t then
    spanM-add (mk-span "Freeness error" (term-start-pos t) (term-end-pos t)
                  (error-data ("A parameter of the datatype occurs free in the erased "
                              ^ "definition of a constructor (this is not allowed)")
                 :: ("the parameter" , x)
                 :: [])) ≫span r
  else r
check-params-not-free (DeclsNil x) t = spanMok

-- see comment for rec-add-ctor-defs below.  We will also add a span for the ctordecl and udef at this point
rec-add-ctor-def : ctxt → string → type → decls → ctordecl → udef → spanM ctxt
rec-add-ctor-def Γ name rectp params (Ctordecl pi x tp) (Udef pi' x' t) =
 spanM-add (Ctordecl-span pi x tp []) ≫span
 (if ~ (x =string x') then
   (spanM-add (Udef-span pi' x' t
                (error-data ("This definition should be for constructor " ^ x 
                           ^ ", since declarations and definitions must be in the same order") :: [])) ≫span spanMr Γ)
  else
    (check-params-not-free params t ≫span
     spanM-add (Udef-span pi' x t []) ≫span

     {- check the definition against the given type, with the definition itself
        substituted for the "self" variable. -}
     check-term Γ t (just tp) ≫span

     let tp = forall-bind-decls params (subst-type Γ rectp name tp) in
     let t = erased-lambda-bind-params params (subst-term Γ rectp name t) in
       spanM-add (Var-span pi' x (type-data tp :: [])) ≫span
       spanMr (ctxt-term-def x t tp Γ)))

-- see comment for rec-add-ctor-defs below
rec-add-ctor-defs-ne : ctxt → string → type → decls → ctordeclsne → udefsne → spanM ctxt
rec-add-ctor-defs-ne Γ name rectp params (CtordeclsneStart c) (UdefsneStart u) = 
  rec-add-ctor-def Γ name rectp params c u
rec-add-ctor-defs-ne Γ name rectp params (CtordeclsneNext c cs) (UdefsneNext u us) = 
  rec-add-ctor-def Γ name rectp params c u ≫=span λ Γ → rec-add-ctor-defs-ne Γ name rectp params cs us
rec-add-ctor-defs-ne Γ name rectp params (CtordeclsneNext c cs) (UdefsneStart (Udef pi x t)) = 
  spanM-add (Udef-span pi x t (error-data ("This is the last constructor definition, but it does not correspond to the"
                                        ^ " last constructor declaration earlier in the recursive datatype definiton.") :: []))
  ≫span spanMr Γ
rec-add-ctor-defs-ne Γ name rectp params (CtordeclsneStart (Ctordecl pi x tp)) (UdefsneNext u us) = 
  spanM-add (Ctordecl-span pi x tp (error-data ("This is the last constructor declaration, but it does not correspond to the"
                                        ^ " last constructor definition later in the recursive datatype definiton.") :: []))
  ≫span spanMr Γ

{- add the ctors with their definitions and types to the final ctxt
   (for after the Rec definition has been processed).  The types and
   definitions of the ctors will be prepended with the given
   parameters, marked as erased (and in the definitions, we will check
   that they are not free except in erased positions). rectype should
   be the name of the recursive type, applied to the parameters.  We
   will substitute this for the recursive type's name in the types of
   the ctors. We will also check the udefs against the types given in 
   ctordecls. -}
rec-add-ctor-defs : ctxt → string → type → decls → ctordecls → udefs → spanM ctxt
rec-add-ctor-defs Γ name rectp params (Ctordeclse _) (Udefse _) = spanMr Γ
rec-add-ctor-defs Γ name rectp params (Ctordeclsne cs) (Udefsne us) = rec-add-ctor-defs-ne Γ name rectp params cs us
rec-add-ctor-defs Γ name rectp params (Ctordeclsne cs) (Udefse pi) = 
  spanM-add (Udefse-span pi
              [ error-data ("There are no constructor definitions here," 
                         ^ " but there are constructor declarations earlier in the recursive type definition") ])
  ≫span spanMr Γ
rec-add-ctor-defs Γ name rectp params (Ctordeclse pi) (Udefsne _) = 
  spanM-add (Ctordeclse-span pi
              [ error-data ("There are no constructor declarations here," 
                         ^ " but there are constructor definitions later in the recursive type definition") ])
  ≫span spanMr Γ

process-rec-cmd : ctxt → posinfo → var → decls → indices → ctordecls → type → udefs → posinfo → spanM ctxt
process-rec-cmd Γ pi name params inds ctors body us pi' = 
  let inds = indices-to-decls inds in
  rec-check-and-add-decls param Γ params ≫=span λ Γp → 

  -- check the indices, in the ctxt containing the params
  rec-check-and-add-decls index Γp inds ≫=span λ Γpi → 

  spanM-add (RecPrelim-span name (decls-start-pos params) (ctordecls-end-pos ctors)) ≫span

    let bind-indices = decls-pi-bind-kind inds in

    let k = bind-indices star in 
    let Γpt = ctxt-type-decl name k Γp in

      {- check the ctors, in the ctxt containing just the params and the recursive type itself,
         adding the new definitions to the context containing the params and the indices -}
      rec-check-and-add-ctors Γpt Γpi ctors ≫=span λ Γpic →

      let nametp = TpVar posinfo-gen name in
      let Γpicts = ctxt-term-decl self-name (rec-apply-decls nametp inds)
                  (ctxt-type-decl name k Γpic) in

      check-type Γpicts body (just star) ≫span

      let k = decls-pi-bind-kind params (bind-indices star) in
      
      -- the recursive type applied to the parameters
      let rectp = rec-apply-decls nametp params in
      let body = forall-bind-decls params (forall-bind-decls inds (Abs posinfo-gen Iota self-name (Tkt nametp) body)) in

        spanM-add (Udefs-span us) ≫span
        spanM-add (Rec-span pi pi' k) ≫span 
        rec-add-ctor-defs (ctxt-rec-def name body k Γ) name rectp params ctors us 

{-  let inds = indices-to-decls inds in
  let p = (rec-compute-kind Γ params inds ≫=span λ k → 
          
          spanMr k) ss
  in
  let k = fst p in
  let ss' = snd p in
  let extra = params ++decls inds in
  let body' = decls-lambda-bind-kind extra body in
-}

