module classify where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import spans
open import syntax-util
open import to-string

unimplemented : spanM ⊤
unimplemented = spanMok

check-term : ctxt → term → type → spanM ⊤
check-type : ctxt → type → kind → spanM ⊤
check-kind : ctxt → kind → spanM ⊤
check-tk : ctxt → tk → spanM ⊤

-- synthc-X means "synthesize the classifier for a X"
synthc-term : ctxt → term → spanM (maybe type)
synthc-type : ctxt → type → spanM (maybe kind)

check-term Γ t tp = unimplemented

check-type Γ (TpParens pi t pi') k = 
  spanM-add (parens-span pi pi') ≫span check-type Γ t k
check-type Γ (TpVar pi x) k with ctxt-lookup-kind Γ x
check-type Γ (TpVar pi x) k | nothing = spanM-add (TpVar-span x pi 
                                                     (error-data "Missing a kind for a type variable." ::
                                                      expected-kind k ::
                                                      missing-kind ::
                                                      []))
check-type Γ (TpVar pi x) k | just k' = if conv-kind Γ k k' 
                                        then spanM-add (TpVar-span x pi 
                                                         ((kind-data k') :: []))
                                        else spanM-add (TpVar-span x pi 
                                                         (error-data "The computed kind does not match the expected kind." :: 
                                                          expected-kind k ::
                                                          kind-data k' ::
                                                          []))
check-type Γ (TpAppt tp t) k =
  synthc-type Γ tp ≫=spanj cont
  
  where cont : kind → spanM ⊤
        cont (KndParens _ k _) = cont k
        cont (KndTpArrow tp' k') = 
          check-term Γ t tp' ≫span
          if conv-kind Γ k k' then spanM-add (TpAppt-span tp t ((kind-data k') :: []))
          else spanM-add (TpAppt-span tp t 
                           (error-data "The return kind for the head of a type application does not match the expected kind." ::
                            expected-kind k ::
                            head-kind k ::
                            ("the return part of the kind of the head" , kind-to-string k') ::
                            []))
        cont k' = spanM-add (TpAppt-span tp t
                               (error-data ("The kind computed for the head of the type application does"
                                        ^ " not allow the head to be applied to an argument which is a term")
                            :: type-app-head tp
                            :: head-kind k' 
                            :: term-argument t
                            :: []))

check-type Γ t k = unimplemented

check-kind Γ (Star pi) = spanM-add (mk-span Star-name pi (posinfo-plus pi 1) [])
check-kind Γ k = unimplemented

check-tk Γ (Tkk k) = check-kind Γ k
check-tk Γ (Tkt t) = check-type Γ t (Star posinfo-gen)


synthc-term Γ t = spanMr nothing

synthc-type Γ (TpParens pi tp pi') = spanM-add (parens-span pi pi') ≫span synthc-type Γ tp
synthc-type Γ (TpVar pi x) with ctxt-lookup-kind Γ x
synthc-type Γ (TpVar pi x) | nothing = 
  spanM-add (TpVar-span x pi (error-data "Undeclared type variable" :: [])) ≫span spanMr nothing
synthc-type Γ (TpVar pi x) | just k = 
  spanM-add (TpVar-span x pi (kind-data k :: [])) ≫span spanMr (just k)
synthc-type Γ t = spanMr nothing
