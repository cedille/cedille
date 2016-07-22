{- code for checking recursive type definitions. -}
module rec where

open import lib

open import cedille-types
open import classify
open import constants
open import conversion
open import ctxt
open import general-util
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
      KndPi posinfo-gen posinfo-gen x atk k'
    else
      tk-arrow-kind atk k'

{- check the given declaration, and return a new context binding the name in the declaration.

   The boolean tells if this is a parameter (tt) or an index (ff). -}
rec-check-and-add-decl : decl-class → ctxt → decl → spanM ctxt
rec-check-and-add-decl dc Γ (Decl pi x atk pi') = 
  check-tk Γ atk ≫span 
  spanM-add (Decl-span dc pi x atk pi') ≫span
  spanMr (ctxt-tk-decl pi x atk Γ)

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
  spanMr (ctxt-term-decl pi x tp Γ')

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

-- return tt iff the variables are not free in the term
check-not-free : string → 𝕃 var → term → spanM 𝔹
check-not-free name (x :: xs) t = 
  check-not-free name xs t ≫=span λ b → 
    if is-free-in-term skip-erased x t then
      spanM-add (mk-span "Freeness error" (term-start-pos t) (term-end-pos t)
                    (error-data ("A " ^ name ^ " of the datatype occurs free in the erased "
                               ^ "definition of a constructor (this is not allowed)")
                 :: ("the " ^ name , x)
                 :: [])) ≫span spanMr ff
    else spanMr b
check-not-free name [] t = spanMr tt

decls-to-vars : decls → 𝕃 var 
decls-to-vars (DeclsCons (Decl _ x _ _) ds) = x :: (decls-to-vars ds)
decls-to-vars (DeclsNil _) = []

ctordeclsne-to-vars : ctordeclsne → 𝕃 var 
ctordeclsne-to-vars (CtordeclsneStart (Ctordecl _ x _)) = [ x ]
ctordeclsne-to-vars (CtordeclsneNext (Ctordecl _ x _) cs) = x :: (ctordeclsne-to-vars cs)

-- see comment for rec-add-ctor-defs below.  We will also add a span for the ctordecl and udef at this point
rec-check-and-add-ctor-def : (no-need-to-check : 𝔹) → 
                             ctxt → ctxt → string → type → decls → ctordeclsne → ℕ → ctordecl → udef → spanM ctxt
rec-check-and-add-ctor-def no-need-to-check Γ Γ' name rectp params ctors whichdecl (Ctordecl pi x tp) (Udef pi' x' t) =
 let tp' = forall-bind-decls params (subst-type Γ rectp name tp) in
 let t' = erase-term t in -- do not lambda-bind the params for t, because they just get erased
  (if no-need-to-check then
    spanMok
  else
   (spanM-add (Ctordecl-span pi x tp []) ≫span
   (if ~ (x =string x') then
     (spanM-add (Udef-span pi' x' (term-end-pos t) (erase-term t)
                  (error-data ("This definition should be for constructor " ^ x 
                             ^ ", since declarations and definitions must be in the same order") :: [])))
    else
     -- we check that the previous ctors are not free in the body of this ctordecl
     (check-not-free "parameter" (decls-to-vars params) t ≫=span λ _ → 
      check-not-free "constructor" (take whichdecl (ctordeclsne-to-vars ctors)) t ≫=span λ b → 
       (if b then 
        (check-term Γ t (just tp))
       else -- do not try to type check the term if a constructor is used in it, as this can lead to divergence
        spanMok) ≫span
        spanM-add (Udef-span pi' x (term-end-pos t) t' [ type-data tp' ]))))) ≫span
    spanMr (ctxt-term-def pi x t' tp' Γ')

-- see comment for rec-check-and-add-ctor-defs below
rec-check-and-add-ctor-defs-ne : (no-need-to-check : 𝔹) → 
                                 ctxt → ctxt → string → type → decls → ℕ → ctordeclsne → udefsne → spanM ctxt
rec-check-and-add-ctor-defs-ne no-need-to-check Γ Γ' name rectp params whichdecl (CtordeclsneStart c) (UdefsneStart u) = 
  rec-check-and-add-ctor-def no-need-to-check Γ Γ' name rectp params (CtordeclsneStart c) whichdecl c u
rec-check-and-add-ctor-defs-ne no-need-to-check Γ Γ' name rectp params whichdecl (CtordeclsneNext c cs) (UdefsneNext u us) = 
  rec-check-and-add-ctor-def no-need-to-check Γ Γ' name rectp params (CtordeclsneNext c cs) whichdecl c u ≫=span
  λ Γ' → rec-check-and-add-ctor-defs-ne no-need-to-check Γ Γ' name rectp params (suc whichdecl) cs us
rec-check-and-add-ctor-defs-ne _ Γ Γ' name rectp params whichdecl (CtordeclsneNext c cs) (UdefsneStart (Udef pi x t)) = 
  spanM-add (Udef-span pi x (term-end-pos t) (erase-term t)
                (error-data ("This is the last constructor definition, but it does not correspond to the"
                           ^ " last constructor declaration earlier in the recursive datatype definiton.") :: []))
  ≫span spanMr Γ'
rec-check-and-add-ctor-defs-ne _ Γ Γ' name rectp params whichdecl (CtordeclsneStart (Ctordecl pi x tp)) (UdefsneNext u us) = 
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
rec-check-and-add-ctor-defs : (no-need-to-check : 𝔹) → ctxt → ctxt → string → type → decls → ctordecls → udefs → spanM ctxt
rec-check-and-add-ctor-defs _ Γ Γ' name rectp params (Ctordeclse _) (Udefse _) = spanMr Γ'
rec-check-and-add-ctor-defs no-need-to-check Γ Γ' name rectp params (Ctordeclsne cs) (Udefsne us) = 
  rec-check-and-add-ctor-defs-ne no-need-to-check Γ Γ' name rectp params 0 cs us
rec-check-and-add-ctor-defs _ Γ Γ' name rectp params (Ctordeclsne cs) (Udefse pi) = 
  spanM-add (Udefse-span pi
              [ error-data ("There are no constructor definitions here," 
                         ^ " but there are constructor declarations earlier in the recursive type definition") ])
  ≫span spanMr Γ'
rec-check-and-add-ctor-defs _ Γ Γ' name rectp params (Ctordeclse pi) (Udefsne _) = 
  spanM-add (Ctordeclse-span pi
              [ error-data ("There are no constructor declarations here," 
                         ^ " but there are constructor definitions later in the recursive type definition") ])
  ≫span spanMr Γ'

rec-add-udef : ctxt → udef → ctxt
rec-add-udef Γ (Udef pi x t) = ctxt-term-udef pi x (hnf Γ no-unfolding t) Γ

rec-add-udefsne : ctxt → udefsne → ctxt
rec-add-udefsne Γ (UdefsneStart u) = rec-add-udef Γ u
rec-add-udefsne Γ (UdefsneNext u us) = rec-add-udefsne (rec-add-udef Γ u) us

rec-add-udefs : ctxt → udefs → ctxt
rec-add-udefs Γ (Udefse _) = Γ
rec-add-udefs Γ (Udefsne us) = rec-add-udefsne Γ us

process-rec-cmd : (no-need-to-check : 𝔹) → 
                  ctxt → posinfo → posinfo → var → decls → indices → ctordecls → type → udefs → posinfo → spanM ctxt
process-rec-cmd no-need-to-check Γ pi pi'' name params inds ctors body us pi' = 
  let inds = indices-to-decls inds in
  let bind-indices = decls-pi-bind-kind inds in
  let k1 = bind-indices star in
  let k2 = decls-pi-bind-kind params k1 in
  let nametp = TpVar posinfo-gen name in
  let rectp = rec-apply-decls nametp params in  -- the recursive type applied to the parameters
  let uses-self = is-free-in check-erased self-name body in
  let body1 = tplam-bind-decls inds (if uses-self then (Iota posinfo-gen self-name NoClass body) else body) in
  let body2 = let body' = subst-type Γ rectp name body in
                   tplam-bind-decls params
                   (tplam-bind-decls inds 
                     (if uses-self then 
                        (Iota posinfo-gen self-name (SomeClass (Tkt rectp)) body')
                      else body')) in

    (if no-need-to-check then
      spanMok
     else
      (rec-check-and-add-decls param Γ params ≫=span λ Γp → 

       -- check the indices, in the ctxt containing the params
       rec-check-and-add-decls index Γp inds ≫=span λ Γpi → 

       spanM-add (RecPrelim-span name (decls-start-pos params) (ctordecls-end-pos ctors)) ≫span

       let k = bind-indices star in 
       let Γpt = ctxt-type-decl pi'' name k Γp in

        {- check the ctors, in the ctxt containing just the params and the recursive type itself,
           adding the new definitions to the context containing the params and the indices -}
        rec-check-and-add-ctors Γpt Γpi ctors ≫=span λ Γpic →

        let Γpicts = ctxt-term-decl posinfo-gen self-name (rec-apply-decls nametp inds)
                    (ctxt-type-decl pi'' name k Γpic) in

         check-type Γpicts body (just star) ≫span

           spanM-add (rectype-name-span pi'' name body2 k2 checking) ≫span
           spanM-add (Udefs-span us) ≫span
           spanM-add (Rec-span pi pi' k2)))
     ≫span 

        {- first we check and add the ctors where the type and the
           body do not bind the params.  We do this in an extended
           ctxt Γctors, which
              1. defines the type to be the body with a self-type
                 abstraction and the indices bound, 
              2. adds the definitions of the ctors (from the udefs) -- up to here this is Γ' -- and
              3. adds types for the ctors (this is the first call to rec-check-and-add-ctor-defs,
                 where no-need-to-check is set to be tt; all we are doing is adding the typings
                 for the ctors).  

           We need both the types and the definitions of the ctors
           for typing each ctor definition.  We cannot cheat, because
           rec-check-and-add-ctor-def enforces that the ctor cannot
           be used in its own definiton except in an erased position.

           The definitions are added to a new ctxt, Γfinal.  Those
           definitions ctors will include the params.  Finally we
           declare the type in Γfinal to include the params. -}
        
        let Γ' = rec-add-udefs (ctxt-rec-def pi'' name body1 k1 Γ) us in

        rec-check-and-add-ctor-defs tt {- do not check -} Γ' Γ' name rectp params ctors us ≫=spand λ Γctors → 

        rec-check-and-add-ctor-defs no-need-to-check Γctors Γ name rectp params ctors us ≫=span λ Γfinal →
        spanMr (ctxt-rec-def pi'' name body2 k2 Γfinal)
