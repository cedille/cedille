module lift where

open import lib

open import cedille-types
open import defeq
open import rename
open import syntax-util
open import subst
open import tpstate

lift-to-kind : tpstate → bctxt → renamectxt → liftingType → kind
lift-to-kind s b r (LiftArrow (LiftParens ltp1) ltp2) = lift-to-kind s b r (LiftArrow ltp1 ltp2)
lift-to-kind s b r (LiftTpArrow tp ltp) = KndTpArrow tp (lift-to-kind s b r ltp)
lift-to-kind s b r (LiftArrow ltp1 ltp2) = KndArrow (lift-to-kind s b r ltp1) (lift-to-kind s b r ltp2)
lift-to-kind s b r LiftStar = Star
lift-to-kind s b r (LiftPi x tp ltp) = 
  let x' = rename-away s b r x in
    KndPi x' (Tkt tp) (lift-to-kind s (bctxt-add b x') (renamectxt-insert r x x') ltp)
lift-to-kind s b r (LiftParens ltp) = lift-to-kind s b r ltp

do-lifth-wrap : bctxt → renamectxt → 𝕃 (var × liftingType) → term → 𝕃 term → liftingType → type
do-lifth-wrap b r vls h args ltp = 
  let vls = reverse vls in 
  let vs = map fst vls in
  let tps = map snd vls in
  let trm : term
      trm = lambdas vs (app-spine h args) in
    rename-type r (bctxt-contains b)
     (type-app-spine (Lft trm (lift-arrows tps ltp)) (map TpVar vs))

{-# NO_TERMINATION_CHECK #-}
do-lifth : tpstate → bctxt → renamectxt → (trie liftingType) → (𝕃 (var × liftingType)) →  
           term → liftingType → type
do-lifth-spine : tpstate → bctxt → renamectxt → (trie liftingType) → (𝕃 (var × liftingType)) →  
                 term → 𝕃 term → liftingType → type
do-lifth-spine-apply : tpstate → bctxt → renamectxt → (trie liftingType) → (𝕃 (var × liftingType)) →  
                       type → liftingType → 𝕃 term → type
do-lifth s b r θ vls (Parens t) ltp = do-lifth s b r θ vls t ltp
do-lifth s b r θ vls t (LiftParens ltp) = do-lifth s b r θ vls t ltp
do-lifth s b r θ vls (Lam y t) (LiftArrow ltp1 ltp2) = 
  let y' : var 
      y' = rename-away s b r y in
    AbsTp2 Lambda y' (Tkk (lift-to-kind s b r ltp1)) 
      (do-lifth s (bctxt-add b y') (renamectxt-insert r y y') (trie-insert θ y' ltp1) ((y' , ltp1) :: vls) t ltp2)
do-lifth s b r θ vls (Var y) ltp with lookup-term-var s (renamectxt-rep r y)
do-lifth s b r θ vls (Var y) ltp | just trm = 
  do-lifth s b r θ vls trm ltp -- this is so that lifting 'λ x . definedvar' will go through the definition
do-lifth s b r θ vls (Var y) ltp | nothing = do-lifth-spine s b r θ vls (Var y) [] ltp 
do-lifth s b r θ vls (App t1 t2) ltp = 
  let a = spine-form (App t1 t2) in
    do-lifth-spine s b r θ vls (fst a) (snd a) ltp
do-lifth s b r θ vls trm ltp = TpVar "internal-error-should-not-happen"

do-lifth-spine s b r θ vls (Var y) args ltp with trie-lookup θ (renamectxt-rep r y)
do-lifth-spine s b r θ vls (Var y) args ltp | nothing = do-lifth-wrap b r vls (Var y) args ltp
do-lifth-spine s b r θ vls (Var y) args ltp | just ltp' = 
  do-lifth-spine-apply s b r θ vls (TpVar (renamectxt-rep r y)) ltp' args
do-lifth-spine s b r θ vls t args ltp = do-lifth-wrap b r vls t args ltp

do-lifth-spine-apply s b r θ vls h ltp [] = h 
do-lifth-spine-apply s b r θ vls h (LiftArrow ltp1 ltp2) (t :: ts) = 
  do-lifth-spine-apply s b r θ vls (TpApp h (do-lifth s b r θ vls t ltp1)) ltp2 ts
do-lifth-spine-apply s b r θ vls h _ (t :: ts) = TpVar "unimplemented-do-lifth-spine-apply" 

do-lift : tpstate → bctxt → renamectxt → term → liftingType → type
do-lift s b r trm ltp = do-lifth s b r empty-trie [] trm ltp 

