module lift where

open import lib

open import cedille-types
open import defeq
open import rename
open import syntax-util
open import subst
open import tpstate

do-lifth-wrap : renamectxt → bctxt → 𝕃 (var × liftingType) → var → term → 𝕃 term → liftingType → type
do-lifth-wrap r b vls x h args ltp = 
  let vls = reverse vls in 
  let vs = map fst vls in
  let tps = map snd vls in
    rename-type r (bctxt-contains b)
     (type-app-spine (Lft x (lambdas vs (app-spine h args)) (lift-arrows tps ltp)) (map TpVar vs))


{-# NO_TERMINATION_CHECK #-}
do-lifth : tpstate → bctxt → renamectxt → (trie liftingType) → (𝕃 (var × liftingType)) →  
           var {- the lifting var -} → term → liftingType → type
do-lifth-spine : tpstate → bctxt → renamectxt → (trie liftingType) → (𝕃 (var × liftingType)) →  
                 var → term → 𝕃 term → liftingType → type
do-lifth-spine-apply : tpstate → bctxt → renamectxt → (trie liftingType) → (𝕃 (var × liftingType)) →  
                       var → type → liftingType → 𝕃 term → type
do-lifth s b r θ vls x (Parens t) ltp = do-lifth s b r θ vls x t ltp
do-lifth s b r θ vls x t (LiftParens ltp) = do-lifth s b r θ vls x t ltp
do-lifth s b r θ vls x (Lam y t) (LiftArrow ltp1 ltp2) = 
  let y' : var 
      y' = rename-away s b r y in
    AbsTp2 Lambda y' (Tkk (lift-to-kind ltp1)) 
      (do-lifth s (bctxt-add b y') (renamectxt-insert r y y') (trie-insert θ y' ltp1) ((y' , ltp1) :: vls) x t ltp2)
do-lifth s b r θ vls x (Var y) ltp with lookup-term-var s (renamectxt-rep r y)
do-lifth s b r θ vls x (Var y) ltp | just trm = 
  do-lifth s b r θ vls x trm ltp -- this is so that lifting 'λ x . definedvar' will go through the definition
do-lifth s b r θ vls x (Var y) ltp | nothing = do-lifth-spine s b r θ vls x (Var y) [] ltp 
do-lifth s b r θ vls x (App t1 t2) ltp = 
  let a = spine-form (App t1 t2) in
    do-lifth-spine s b r θ vls x (fst a) (snd a) ltp
do-lifth s b r θ vls x trm ltp = TpVar "internal-error-should-not-happen"

do-lifth-spine s b r θ vls x (Var y) args ltp with trie-lookup θ (renamectxt-rep r y)
do-lifth-spine s b r θ vls x (Var y) args ltp | nothing = do-lifth-wrap r b vls x (Var y) args ltp
do-lifth-spine s b r θ vls x (Var y) args ltp | just ltp' = 
  do-lifth-spine-apply s b r θ vls x (TpVar (renamectxt-rep r y)) ltp' args
do-lifth-spine s b r θ vls x t args ltp = do-lifth-wrap r b vls x t args ltp

do-lifth-spine-apply s b r θ vls x h ltp [] = h 
do-lifth-spine-apply s b r θ vls x h (LiftArrow ltp1 ltp2) (t :: ts) = 
  do-lifth-spine-apply s b r θ vls x (TpApp h (do-lifth s b r θ vls x t ltp1)) ltp2 ts
do-lifth-spine-apply s b r θ vls  x h _ (t :: ts) = TpVar "unimplemented-do-lifth-spine-apply" 

do-lift : tpstate → bctxt → renamectxt → var → term → liftingType → type
do-lift s b r x trm ltp = do-lifth s b r empty-trie [] x trm ltp 
