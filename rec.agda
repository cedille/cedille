{- code for checking recursive type definitions. -}
module rec where

open import lib

open import cedille-types
open import classify
open import constants
open import ctxt
open import hnf
open import is-free
open import spans
open import subst
open import syntax-util
open import to-string

decls-pi-bind-kind : decls → kind → kind
decls-pi-bind-kind (DeclsNil _) k = k
decls-pi-bind-kind (DeclsCons (Decl _ x atk _) ds) k = 
  let k' = decls-pi-bind-kind ds k in
    if (is-free-in-kind check-erased x k') then
      KndPi posinfo-gen x posinfo-gen atk k'
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
rec-check-and-add-ctor-def : ctxt → ctxt → string → type → decls → ctordecl → udef → spanM ctxt
rec-check-and-add-ctor-def Γ Γ' name rectp params (Ctordecl pi x tp) (Udef pi' x' t) =
 spanM-add (Ctordecl-span pi x tp []) ≫span
 (if ~ (x =string x') then
   (spanM-add (Udef-span pi' x' t ff
                (error-data ("This definition should be for constructor " ^ x 
                           ^ ", since declarations and definitions must be in the same order") :: [])) ≫span spanMr Γ)
  else
    (check-params-not-free params t ≫span
     check-term Γ t (just tp) ≫span

     let tp = forall-bind-decls params (subst-type Γ rectp name tp) in
     -- do not lambda-bind the params, because we are keeping just the erased definition
     let t = hnf Γ ff (subst-term Γ rectp name t) in
       spanM-add (Udef-span pi' x t tt []) ≫span
       spanMr (ctxt-term-def x t tp Γ')))

-- see comment for rec-check-and-add-ctor-defs below
rec-check-and-add-ctor-defs-ne : ctxt → ctxt → string → type → decls → ctordeclsne → udefsne → spanM ctxt
rec-check-and-add-ctor-defs-ne Γ Γ' name rectp params (CtordeclsneStart c) (UdefsneStart u) = 
  rec-check-and-add-ctor-def Γ Γ' name rectp params c u
rec-check-and-add-ctor-defs-ne Γ Γ' name rectp params (CtordeclsneNext c cs) (UdefsneNext u us) = 
  rec-check-and-add-ctor-def Γ Γ' name rectp params c u ≫=span λ Γ' → rec-check-and-add-ctor-defs-ne Γ Γ' name rectp params cs us
rec-check-and-add-ctor-defs-ne Γ Γ' name rectp params (CtordeclsneNext c cs) (UdefsneStart (Udef pi x t)) = 
  spanM-add (Udef-span pi x t ff (error-data ("This is the last constructor definition, but it does not correspond to the"
                                        ^ " last constructor declaration earlier in the recursive datatype definiton.") :: []))
  ≫span spanMr Γ'
rec-check-and-add-ctor-defs-ne Γ Γ' name rectp params (CtordeclsneStart (Ctordecl pi x tp)) (UdefsneNext u us) = 
  spanM-add (Ctordecl-span pi x tp (error-data ("This is the last constructor declaration, but it does not correspond to the"
                                        ^ " last constructor definition later in the recursive datatype definiton.") :: []))
  ≫span spanMr Γ'

{- add the ctors with their definitions and types to the final ctxt
   (for after the Rec definition has been processed).  The types and
   definitions of the ctors will be prepended with the given
   parameters, marked as erased (and in the definitions, we will check
   that they are not free except in erased positions). rectype should
   be the name of the recursive type, applied to the parameters.  We
   will substitute this for the recursive type's name in the types of
   the ctors. We will also check the udefs against the types given in 
   ctordecls. -}
rec-check-and-add-ctor-defs : ctxt → ctxt → string → type → decls → ctordecls → udefs → spanM ctxt
rec-check-and-add-ctor-defs Γ Γ' name rectp params (Ctordeclse _) (Udefse _) = spanMr Γ'
rec-check-and-add-ctor-defs Γ Γ' name rectp params (Ctordeclsne cs) (Udefsne us) = 
  rec-check-and-add-ctor-defs-ne Γ Γ' name rectp params cs us
rec-check-and-add-ctor-defs Γ Γ' name rectp params (Ctordeclsne cs) (Udefse pi) = 
  spanM-add (Udefse-span pi
              [ error-data ("There are no constructor definitions here," 
                         ^ " but there are constructor declarations earlier in the recursive type definition") ])
  ≫span spanMr Γ'
rec-check-and-add-ctor-defs Γ Γ' name rectp params (Ctordeclse pi) (Udefsne _) = 
  spanM-add (Ctordeclse-span pi
              [ error-data ("There are no constructor declarations here," 
                         ^ " but there are constructor definitions later in the recursive type definition") ])
  ≫span spanMr Γ'

rec-add-udef : ctxt → udef → ctxt
rec-add-udef Γ (Udef _ x t) = ctxt-term-udef x (hnf Γ ff t) Γ

rec-add-udefsne : ctxt → udefsne → ctxt
rec-add-udefsne Γ (UdefsneStart u) = rec-add-udef Γ u
rec-add-udefsne Γ (UdefsneNext u us) = rec-add-udefsne (rec-add-udef Γ u) us

rec-add-udefs : ctxt → udefs → ctxt
rec-add-udefs Γ (Udefse _) = Γ
rec-add-udefs Γ (Udefsne us) = rec-add-udefsne Γ us

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

      let k1 = bind-indices star in
      let k2 = decls-pi-bind-kind params k1 in
      
      -- the recursive type applied to the parameters
      let rectp = rec-apply-decls nametp params in
      let body1 = tplam-bind-decls inds (Iota posinfo-gen self-name body) in
      let body2 = tplam-bind-decls params body1 in

        spanM-add (Udefs-span us) ≫span
        spanM-add (Rec-span pi pi' k) ≫span 

        {- first we check and add the ctors where the type and the
           body do not bind the params.  We do this in an extended
           ctxt defining the type to be the body with a self-type
           abstraction and the indices bound, and with the definitions
           for the udefs added to the ctxt.  The definitions are added
           to a new ctxt, Γfinal.  Those definitions ctors will include
           the params.  Finally we declare the type in Γfinal to 
           include the params. -}

        rec-check-and-add-ctor-defs (rec-add-udefs (ctxt-rec-def name body1 k1 Γ) us) Γ name rectp params ctors us ≫=span λ Γfinal → 
          spanMr (ctxt-rec-def name body2 k2 Γfinal)
