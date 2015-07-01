module defeq where

open import lib
open import cedille-types
open import rename 
open import tpstate

{- we will rename variables away from strings recognized by the given
   predicate.  Currently, we are not checking termination, though this
   could maybe be done by bounding the size of the domain of the
   tpstate.  This size would decrease when we follow a definition. -}

-- the predicate just needs to return tt for bound local variables (not global ones)

eq-ip : ip → ip → 𝔹
eq-ip Iota Iota = tt
eq-ip Iota Pi = ff
eq-ip Pi Iota = ff
eq-ip Pi Pi = tt

eq-al : al → al → 𝔹
eq-al All All = tt
eq-al All Lambda = ff
eq-al Lambda All = ff
eq-al Lambda Lambda = tt

{-# NO_TERMINATION_CHECK #-}
eq-kind : tpstate → (var → 𝔹) → renamectxt → kind → kind → 𝔹 
eq-type : tpstate → (var → 𝔹) → renamectxt → type → type → 𝔹 
eq-kind-pi : tpstate → (var → 𝔹) → renamectxt → var → tk → kind → kind → 𝔹 
eq-kind-pi1 : tpstate → (var → 𝔹) → renamectxt → var → tk → kind → kind → 𝔹 
eq-ctorset : tpstate → (var → 𝔹) → renamectxt → ctorset → ctorset → 𝔹
eq-term : tpstate → (var → 𝔹) → renamectxt → term → term → 𝔹
eq-term-var : tpstate → (var → 𝔹) → renamectxt → var → term → 𝔹
eq-type-var : tpstate → (var → 𝔹) → renamectxt → var → type → 𝔹
eq-tk : tpstate → (var → 𝔹) → renamectxt → tk → tk → 𝔹
eq-type-arrow : tpstate → (var → 𝔹) → renamectxt → var → type → type → type → type → 𝔹
eq-liftingType : tpstate → (var → 𝔹) → renamectxt → liftingType → liftingType → 𝔹 
eq-kind s b r (KndParens k) k' = eq-kind s b r k k'
eq-kind s b r k (KndParens k') = eq-kind s b r k k'
eq-kind s b r (KndArrow k1 k2) k' = eq-kind-pi s b r (tpstate-fresh-var s b "X" r) (Tkk k1) k2 k'
eq-kind s b r k (KndArrow k1' k2') = eq-kind-pi s b r (tpstate-fresh-var s b "X" r) (Tkk k1') k2' k
eq-kind s b r (KndTpArrow t k) k' = eq-kind-pi s b r (tpstate-fresh-var s b "x" r) (Tkt t) k k'
eq-kind s b r k (KndTpArrow t' k') = eq-kind-pi s b r (tpstate-fresh-var s b "x" r) (Tkt t') k' k
eq-kind s b r (KndPi x (Tkk k1) k2) k = eq-kind-pi1 s b r x (Tkk k1) k2 k
eq-kind s b r k (KndPi x' (Tkk k1') k2') = eq-kind-pi1 s b r x' (Tkk k1') k2' k
eq-kind s b r (KndPi x (Tkt t) k) k' = eq-kind-pi1 s b r x (Tkt t) k k'
eq-kind s b r k (KndPi x' (Tkt t') k') = eq-kind-pi1 s b r x' (Tkt t') k' k
eq-kind s b r Star Star = tt
eq-kind s b r k (KndVar v) with lookup-kind-var s v
eq-kind s b r k (KndVar v) | just k' = eq-kind s b r k k'
eq-kind s b r k (KndVar v) | nothing = ff
eq-kind s b r (KndVar v) k' with lookup-kind-var s v
eq-kind s b r (KndVar v) k' | just k = eq-kind s b r k k'
eq-kind s b r (KndVar v) k' | nothing = ff

-- X is not assumed to be the result of renaming, and we will rename it
eq-kind-pi1 s b r X a k k' = 
  let X' = rename-away' s b r X in
    eq-kind-pi s b (renamectxt-insert r X X') X' a k k'

-- X is assumed to be the result of renaming
eq-kind-pi s b r X a k2 (KndParens k) = eq-kind-pi s b r X a k2 k -- redundant case, but Agda can't tell
eq-kind-pi s b r X (Tkk k1) k2 (KndArrow k1' k2') = eq-kind s b r k1 k1' && eq-kind s b r k2 k2'
eq-kind-pi s b r X (Tkk k1) k2 (KndPi v (Tkk k1') k2') = 
  eq-kind s b r k1 k1' && eq-kind s b (renamectxt-insert r v X) k2 k2'
eq-kind-pi s b r X (Tkk k1) k2 (KndPi x (Tkt _) k') = ff
eq-kind-pi s b r X (Tkk k1) k2 (KndTpArrow x k') = ff
eq-kind-pi s b r X a k2 (KndVar x) with lookup-kind-var s (renamectxt-rep r x)
eq-kind-pi s b r X a k2 (KndVar x) | just k = eq-kind-pi s b r X a k2 k
eq-kind-pi s b r X a k2 (KndVar x) | nothing = ff
eq-kind-pi s b r X (Tkk k1) k2 Star = ff
eq-kind-pi s b r X (Tkt t) k (KndTpArrow t' k') = eq-type s b r t t' && eq-kind s b r k k'
eq-kind-pi s b r X (Tkt t) k (KndPi x (Tkt t') k') =
  eq-type s b r t t' && eq-kind s b (renamectxt-insert r x X) k k'
eq-kind-pi s b r X (Tkt t) k (KndPi v (Tkk _) k2') = ff
eq-kind-pi s b r X (Tkt t) k (KndArrow k1' k2') = ff
eq-kind-pi s b r X (Tkt t) k Star = ff

eq-tk s b r (Tkk k1) (Tkk k2) = eq-kind s b r k1 k2
eq-tk s b r (Tkt k1) (Tkt k2) = eq-type s b r k1 k2
eq-tk s b r _ _ = ff

eq-term s b r t (Parens t') = eq-term s b r t t'
eq-term s b r (Parens t) t' = eq-term s b r t t'
eq-term s b r (App t1 t2) (App t1' t2') = eq-term s b r t1 t1' && eq-term s b r t2 t2'
eq-term s b r (Var x) t' = eq-term-var s b r x t'
eq-term s b r t (Var x) = eq-term-var s b r x t
eq-term s b r (Lam x1 t1) (Lam x2 t2) =
  eq-term s b (renamectxt-insert r x1 x2) t1 t2
eq-term s b r (Lam _ _) (App _ _) = ff
eq-term s b r (App _ _) (Lam _ _) = ff

eq-term-var s b r x t' with lookup-term-var s (renamectxt-rep r x) 
eq-term-var s b r x t' | just t = eq-term s b r t t'
eq-term-var s b r x (Var y) | nothing with lookup-term-var s (renamectxt-rep r y)
eq-term-var s b r x (Var y) | nothing | just t' = eq-term-var s b r x t'
eq-term-var s b r x (Var y) | nothing | nothing = eq-var r x y
eq-term-var s b r x (Parens t) | nothing = eq-term-var s b r x t
eq-term-var s b r x _ | nothing = ff

eq-type s b r (TpParens t) t' = eq-type s b r t t' 
eq-type s b r t (TpParens t') = eq-type s b r t t' 
eq-type s b r (TpVar x) t' = eq-type-var s b r x t'
eq-type s b r t (TpVar x) = eq-type-var s b r x t
eq-type s b r (TpApp t1 t2) (TpApp t1' t2') = eq-type s b r t1 t1' && eq-type s b r t2 t2'
eq-type s b r (TpArrow t1 t2) (TpArrow t1' t2') = eq-type s b r t1 t1' && eq-type s b r t2 t2'
eq-type s b r (TpAppt t1 t2) (TpAppt t1' t2') = eq-type s b r t1 t1' && eq-term s b r t2 t2'
eq-type s b r (AbsTp1 o x tp1 tp2) (AbsTp1 o' x' tp1' tp2') = 
  let x'' = rename-away' s b r x in
  let r' = renamectxt-insert (renamectxt-insert r x x'') x' x'' in
    eq-ip o o' && eq-type s b r tp1 tp1' && eq-type s b r' tp2 tp2'
eq-type s b r (AbsTp1 o' x tp1' tp2') (TpArrow tp1 tp2) = eq-type-arrow s b r x tp1 tp2 tp1' tp2'
eq-type s b r (TpArrow tp1 tp2) (AbsTp1 o' x tp1' tp2') = eq-type-arrow s b r x tp1 tp2 tp1' tp2'
eq-type s b r (AbsTp2 o x a tp) (AbsTp2 o' x' a' tp') = 
  let x'' = rename-away' s b r x in
  let r' = renamectxt-insert (renamectxt-insert r x x'') x' x'' in
    eq-al o o' && eq-tk s b r a a' && eq-type s b r' tp tp'
eq-type s b r (Lft t T) (Lft t' T') = 
    eq-term s b r t t' && eq-liftingType s b r T T'
eq-type s b r U U = tt 
eq-type s b r (Nu x k Θ t) (Nu x' k' Θ' t') = 
  let x'' = rename-away' s b r x in
  let r' = renamectxt-insert (renamectxt-insert r x x'') x' x'' in
    eq-kind s b r k k' && eq-ctorset s b r' Θ Θ' && eq-type s b r' t t'
eq-type s b r _ _ = ff 

eq-type-arrow s b r x tp1 tp2 tp1' tp2' =
  let x' = rename-away' s b r x in
    eq-type s b r tp1 tp1' && eq-type s b (renamectxt-insert r x x') tp2 tp2'

eq-type-var s b r x t' with lookup-type-var s (renamectxt-rep r x) 
eq-type-var s b r x t' | just t = eq-type s b r t t'
eq-type-var s b r x (TpVar y) | nothing with lookup-type-var s (renamectxt-rep r y)
eq-type-var s b r x (TpVar y) | nothing | just t' = eq-type-var s b r x t'
eq-type-var s b r x (TpVar y) | nothing | nothing = eq-var r x y
eq-type-var s b r x (TpParens t) | nothing = eq-type-var s b r x t
eq-type-var s b r x _ | nothing = ff

eq-liftingType s b r (LiftParens l) l' = eq-liftingType s b r l l' 
eq-liftingType s b r l (LiftParens l') = eq-liftingType s b r l l' 
eq-liftingType s b r (LiftArrow l1 l2) (LiftArrow l1' l2') = 
  eq-liftingType s b r l1 l1' && eq-liftingType s b r l2 l2'
eq-liftingType s b r (LiftTpArrow t l) (LiftTpArrow t' l') = 
  eq-type s b r t t' && eq-liftingType s b r l l'
eq-liftingType s b r (LiftPi x t l) (LiftPi x' t' l') = 
  let x'' = rename-away' s b r x in
  let r' = renamectxt-insert (renamectxt-insert r x x'') x' x'' in
    eq-type s b r t t' && eq-liftingType s b r' l l'
eq-liftingType s b r LiftStar LiftStar = tt
eq-liftingType s b r _ _ = ff

eq-ctorset s b r (Add trm tp Θ) (Add trm' tp' Θ') = eq-term s b r trm trm' && eq-type s b r tp tp' && eq-ctorset s b r Θ Θ'
eq-ctorset s b r (Add x x₁ Θ) Empty = ff
eq-ctorset s b r Empty (Add x x₁ Θ') = ff
eq-ctorset s b r Empty Empty = tt