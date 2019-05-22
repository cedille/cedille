module rename where

open import lib

open import cedille-types 
open import constants
open import ctxt-types
--open import is-free
open import free-vars
open import syntax-util
open import general-util

renamectxt : Set
renamectxt = stringset × trie string  {- the trie maps vars to their renamed versions, 
                                         and the stringset stores all those renamed versions -}

empty-renamectxt : renamectxt
empty-renamectxt = empty-stringset , empty-trie

renamectxt-contains : renamectxt → string → 𝔹
renamectxt-contains (_ , r) s = trie-contains r s

renamectxt-insert : renamectxt → (s1 s2 : string) → renamectxt
renamectxt-insert (ranr , r) s x = stringset-insert ranr x , trie-insert r s x

renamectxt-single : var → var → renamectxt
renamectxt-single = renamectxt-insert empty-renamectxt

renamectxt-lookup : renamectxt → string → maybe string
renamectxt-lookup (ranr , r) s = trie-lookup r s

renamectxt-remove : renamectxt → string → renamectxt
renamectxt-remove (ranr , r) s with trie-lookup r s
renamectxt-remove (ranr , r) s | nothing = ranr , r
renamectxt-remove (ranr , r) s | just s' = stringset-remove ranr s' , trie-remove r s

renamectxt-in-range : renamectxt → string → 𝔹
renamectxt-in-range (ranr , r) s = stringset-contains ranr s

renamectxt-in-field : renamectxt → string → 𝔹
renamectxt-in-field m s = renamectxt-contains m s || renamectxt-in-range m s

renamectxt-rep : renamectxt → string → string
renamectxt-rep r x with renamectxt-lookup r x
renamectxt-rep r x | nothing = x
renamectxt-rep r x | just x' = x'

eq-var : renamectxt → string → string → 𝔹
eq-var r x y = renamectxt-rep r x =string renamectxt-rep r y

{-# NON_TERMINATING #-}
fresh' : (var → 𝔹) → ℕ → var → var
fresh' bound n base with base ^ ℕ-to-string n
...| x with bound x
...| tt = fresh' bound (suc n) base
...| ff = x

fresh-h : (var → 𝔹) → var → var
fresh-h bound x =
  if ~ bound x'
    then x'
    else uncurry (fresh' bound) (fresh-split [] (reverse (string-to-𝕃char x')))
  where
  x' = if x =string ignored-var then "x" else x

  to-num : 𝕃 char → ℕ
  to-num [] = 1
  to-num ns = string-to-ℕ0 (𝕃char-to-string ns)

  fresh-split : 𝕃 char → 𝕃 char → ℕ × var
  fresh-split ns [] = to-num ns , ""
  fresh-split ns (c :: cs) with is-digit c
  ...| tt = fresh-split (c :: ns) cs
  ...| ff = to-num ns , 𝕃char-to-string (reverse (c :: cs))

fresh-var : ctxt → var → var
fresh-var = fresh-h ∘' ctxt-binds-var

fresh-var-renamectxt : ctxt → renamectxt → var → var
fresh-var-renamectxt Γ ρ = fresh-h λ x → ctxt-binds-var Γ x || renamectxt-in-field ρ x
{-
pick-new-name : string → string
pick-new-name x = x ^ "'"
-}
{-
{- rename-away-from x g r rename the variable x to be some new name (related to x)
   which does not satisfy the given predicate on names (assuming this is possible),
   and is not in the domain of the renamectxt . -}
{-# NON_TERMINATING #-}
rename-away-from : string → (string → 𝔹) → renamectxt → string
rename-away-from x g r =
  if (g x) then
    rename-away-from (pick-new-name x) g r
  else if (renamectxt-in-field r x) then
    rename-away-from (pick-new-name x) g r
  else x

fresh-var : string → (string → 𝔹) → renamectxt → string
fresh-var = rename-away-from

fresh-var-new : ctxt → var → var
fresh-var-new Γ ignored-var = fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt
fresh-var-new Γ x = fresh-var x (ctxt-binds-var Γ) empty-renamectxt
-}

rename-var-if : {ed : exprd} → ctxt → renamectxt → var → ⟦ ed ⟧ → var
rename-var-if Γ ρ y t = 
  if is-free-in y t || renamectxt-in-range ρ y then 
    fresh-var-renamectxt Γ ρ y --rename-away-from y (ctxt-binds-var Γ) ρ
  else
    y

renamectxt-insert* : renamectxt → (vs1 vs2 : 𝕃 string) → maybe renamectxt
renamectxt-insert* ρ [] [] = just ρ
renamectxt-insert* ρ (x :: vs1) (y :: vs2) = renamectxt-insert* (renamectxt-insert ρ x y) vs1 vs2
renamectxt-insert* ρ _ _ = nothing
