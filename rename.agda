module rename where

open import lib

open import cedille-types 
open import ctxt
open import is-free
open import syntax-util

renamectxt : Set
renamectxt = trie string

empty-renamectxt : renamectxt
empty-renamectxt = empty-trie

renamectxt-contains : renamectxt → string → 𝔹
renamectxt-contains r s = trie-contains r s

renamectxt-insert : renamectxt → (s1 s2 : string) → renamectxt
renamectxt-insert r s x with s =string x
renamectxt-insert r s x | tt = r
renamectxt-insert r s x | ff = trie-insert r s x

renamectxt-lookup : renamectxt → string → maybe string
renamectxt-lookup = trie-lookup 

renamectxt-remove : renamectxt → string → renamectxt
renamectxt-remove = trie-remove

renamectxt-rep : renamectxt → string → string
renamectxt-rep r x with renamectxt-lookup r x
renamectxt-rep r x | nothing = x
renamectxt-rep r x | just x' = x'

eq-var : renamectxt → string → string → 𝔹
eq-var r x y = renamectxt-rep r x =string renamectxt-rep r y

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

rename-var-if : {ed : exprd} → ctxt → renamectxt → var → ⟦ ed ⟧ → var
rename-var-if Γ ρ y t = 
  if is-free-in check-erased y t then 
    rename-away-from y (ctxt-binds-var Γ) ρ
  else
    y

