module eqs where

open import lib
open import cedille-types
open import rename 
open import tpstate

{- we will rename variables away from strings recognized by the given
   predicate.  Currently, we are not checking termination, though this
   could maybe be done by bounding the size of the domain of the
   tpstate.  This size would decrease when we follow a definition. -}

{-# NO_TERMINATION_CHECK #-}
eq-kindh : tpstate → renamectxt → kind → kind → 𝔹 
eq-typeh-l : tpstate → renamectxt → type → ltype → 𝔹 
eq-typeh : tpstate → renamectxt → type → type → 𝔹 
eq-kindh-pi : tpstate → renamectxt → var → tk → kind → kind → 𝔹 
eq-kindh s r (KndParens k) k' = eq-kindh s r k k'
eq-kindh s r k (KndParens k') = eq-kindh s r k k'
eq-kindh s r (KndArrow k1 k2) k' = eq-kindh-pi s r (fresh-var "X" (in-dom-tpstate s) r) (Tkk k1) k2 k'
eq-kindh s r k (KndArrow k1' k2') = eq-kindh-pi s r (fresh-var "X" (in-dom-tpstate s) r) (Tkk k1') k2' k
eq-kindh s r (KndTpArrow t k) k' = eq-kindh-pi s r (fresh-var "x" (in-dom-tpstate s) r) (Tkt (Ltype t)) k k'
eq-kindh s r k (KndTpArrow t' k') = eq-kindh-pi s r (fresh-var "x" (in-dom-tpstate s) r) (Tkt (Ltype t')) k' k
eq-kindh s r (KndPi x (Tkk k1) k2) k = eq-kindh-pi s r x (Tkk k1) k2 k
eq-kindh s r k (KndPi x' (Tkk k1') k2') = eq-kindh-pi s r x' (Tkk k1') k2' k
eq-kindh s r (KndPi x (Tkt t) k) k' = eq-kindh-pi s r x (Tkt t) k k'
eq-kindh s r k (KndPi x' (Tkt t') k') = eq-kindh-pi s r x' (Tkt t') k' k
eq-kindh s r Star Star = tt
eq-kindh s r k (KndVar v) with lookup-kind-var s v
eq-kindh s r k (KndVar v) | just k' = eq-kindh s r k k'
eq-kindh s r k (KndVar v) | nothing = ff
eq-kindh s r (KndVar v) k' with lookup-kind-var s v
eq-kindh s r (KndVar v) k' | just k = eq-kindh s r k k'
eq-kindh s r (KndVar v) k' | nothing = ff

eq-kindh-pi s r X a k2 (KndParens k) = eq-kindh-pi s r X a k2 k -- redundant case, but Agda can't tell
eq-kindh-pi s r X (Tkk k1) k2 (KndArrow k1' k2') = eq-kindh s r k1 k1' && eq-kindh s r k2 k2'
eq-kindh-pi s r X (Tkk k1) k2 (KndPi v (Tkk k1') k2') = eq-kindh s r k1 k1' && eq-kindh s (renamectxt-insert r X v) k2 k2'
eq-kindh-pi s r X (Tkk k1) k2 (KndPi x (Tkt _) k') = ff
eq-kindh-pi s r X (Tkk k1) k2 (KndTpArrow x k') = ff
eq-kindh-pi s r X a k2 (KndVar x) with lookup-kind-var s x
eq-kindh-pi s r X a k2 (KndVar x) | just k = eq-kindh-pi s r X a k2 k
eq-kindh-pi s r X a k2 (KndVar x) | nothing = ff
eq-kindh-pi s r X (Tkk k1) k2 Star = ff
eq-kindh-pi s r X (Tkt t) k (KndTpArrow t' k') = eq-typeh-l s r t t' && eq-kindh s r k k'
eq-kindh-pi s r X (Tkt t) k (KndPi x (Tkt t') k') = eq-typeh s r t t' && eq-kindh s (renamectxt-insert r X x) k k'
eq-kindh-pi s r X (Tkt t) k (KndPi v (Tkk _) k2') = ff
eq-kindh-pi s r X (Tkt t) k (KndArrow k1' k2') = ff
eq-kindh-pi s r X (Tkt t) k Star = ff

eq-typeh-l s r t l = tt

eq-typeh s r t t' = tt

eq-kind : tpstate → kind → kind → 𝔹 
eq-kind s k k' = eq-kindh s empty-renamectxt k k'