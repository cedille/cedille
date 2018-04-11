{- functions related to lift types.  The main function is do-lift, which
   is called from hnf -}
module lift where

open import lib
open import cedille-types
open import ctxt
open import syntax-util
open import subst

liftingType-to-kind : liftingType → kind
liftingType-to-kind (LiftArrow l1 l2) = KndArrow (liftingType-to-kind l1) (liftingType-to-kind l2)
liftingType-to-kind (LiftStar _) = star
liftingType-to-kind (LiftParens _ l _) = liftingType-to-kind l
liftingType-to-kind (LiftTpArrow tp l) = KndTpArrow tp (liftingType-to-kind l)
liftingType-to-kind (LiftPi _ x tp l) = KndPi posinfo-gen posinfo-gen x (Tkt tp) (liftingType-to-kind l)

liftingType-to-type : var → liftingType → type
liftingType-to-type X (LiftArrow l1 l2) = TpArrow (liftingType-to-type X l1) UnerasedArrow  (liftingType-to-type X l2)
liftingType-to-type X (LiftTpArrow tp l) = TpArrow tp UnerasedArrow (liftingType-to-type X l)
liftingType-to-type X (LiftStar _) = TpVar posinfo-gen X
liftingType-to-type X (LiftParens _ l _) = liftingType-to-type X l
liftingType-to-type X (LiftPi _ x tp l) = Abs posinfo-gen Pi posinfo-gen x (Tkt tp) (liftingType-to-type X l)

{- create a type-level redex of the form

   (↑ X . (λ xs . t) : ls → l) xs

   where xs and ls are packaged as the input list of tuples, l is the
   input liftingType, and t is the input term. -}
lift-freeze : var → 𝕃 (var × liftingType) → liftingType → term → type
lift-freeze X tobind l t = 
  let xs = map fst tobind in
    TpApp* (Lft posinfo-gen posinfo-gen X (Lam* xs t) (LiftArrow* (map snd tobind) l))
      (map (λ p → TpVar posinfo-gen (fst p)) tobind)

do-liftargs : ctxt → type → liftingType → 𝕃 term → var → 𝕃 (var × liftingType) → type
do-liftargs Γ tp (LiftArrow l1 l2) (arg :: args) X tobind =
  do-liftargs Γ (TpApp tp (lift-freeze X tobind l1 arg)) l2 args X tobind
do-liftargs Γ tp (LiftTpArrow l1 l2) (arg :: args) X tobind =
  do-liftargs Γ (TpAppt tp arg) l2 args X tobind
do-liftargs Γ tp (LiftPi _ x _ l) (arg :: args) X tobind =
  do-liftargs Γ (TpAppt tp arg) (subst-liftingType Γ arg x l) args X tobind
do-liftargs Γ tp (LiftParens _ l _) args X tobind = do-liftargs Γ tp l args X tobind 
do-liftargs Γ tp _ _ _ _ = tp

-- tobind are the variables we have seen going through the lifting type (they are also mapped by the trie)
do-lifth : ctxt → trie liftingType →
           𝕃 (var × liftingType) → type → var → liftingType → 
           (term → term) → -- function to put terms in hnf
           term →           
           type
do-lifth Γ m tobind origtp X (LiftParens _ l _) hnf t = do-lifth Γ m tobind origtp X l hnf t 
do-lifth Γ m tobind origtp X (LiftArrow l1 l2) hnf (Lam _ _ _ x _ t) = 
  do-lifth Γ (trie-insert m x l1) ((x , l1) :: tobind) origtp X l2 hnf t
do-lifth Γ m tobind origtp X (LiftTpArrow tp l2) hnf (Lam _ _ _ x _ t) = 
  TpLambda posinfo-gen posinfo-gen x (Tkt tp) (do-lifth Γ m tobind origtp X l2 hnf t)
do-lifth Γ m tobind origtp X l hnf t with decompose-apps (hnf t)
do-lifth Γ m tobind origtp X l hnf t | (Var _ x) , args with trie-lookup m x
do-lifth Γ m tobind origtp X l hnf t | (Var _ x) , args | nothing = origtp -- the term being lifted is not headed by one of the bound vars
do-lifth Γ m tobind origtp X l hnf t | (Var _ x) , args | just l' = 
  rebind tobind (do-liftargs Γ (TpVar posinfo-gen x) l' (reverse args) X tobind)
  where rebind : 𝕃 (var × liftingType) → type → type
        rebind ((x , l'):: xs) tp = rebind xs (TpLambda posinfo-gen posinfo-gen x (Tkk (liftingType-to-kind l')) tp)
        rebind [] tp = tp 
do-lifth Γ m tobind origtp X l hnf t | _ , args = origtp

-- lift a term to a type at the given liftingType, if possible.
do-lift : ctxt → type → var → liftingType → (term → term) {- hnf -} → term → type
do-lift Γ origtp X l hnf t = do-lifth Γ empty-trie [] origtp X l hnf t

