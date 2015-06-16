module rename where

open import lib

{- map variable names to variable names, but make sure that if we map x to y, we also map y to x -}
renamectxt : Set
renamectxt = trie string

empty-renamectxt : renamectxt
empty-renamectxt = empty-trie

renamectxt-contains : renamectxt → string → 𝔹
renamectxt-contains r s = trie-contains r s

renamectxt-insert : renamectxt → string → string → renamectxt
renamectxt-insert r s x = trie-insert r s x

eq-var : renamectxt → string → string → 𝔹
eq-var r x y with x =string y
eq-var r x y | tt = tt
eq-var r x y | ff with trie-lookup r x
eq-var r x y | ff | just x' = y =string x'
eq-var r x y | ff | nothing with trie-lookup r y
eq-var r x y | ff | nothing | just y' = x =string y'
eq-var r x y | ff | nothing | nothing = ff

pick-new-name : string → string
pick-new-name x = x ^ "'"

{- rename-away-from x g r rename the variable x to be some new name (related to x)
   which does not satisfy the given predicate on names (assuming this is possible),
   and is not in the domain of the renamectxt . -}
{-# NO_TERMINATION_CHECK #-}
rename-away-from : string → (string → 𝔹) → renamectxt → string
rename-away-from x g r =
  if (g x) then
    rename-away-from (pick-new-name x) g r
  else if (renamectxt-contains r x) then
    rename-away-from (pick-new-name x) g r
  else x

fresh-var : string → (string → 𝔹) → renamectxt → string
fresh-var = rename-away-from