{-# OPTIONS --no-positivity-check #-}
module format where

open import lib

data formatti : Set where
  iarg : formatti
  inone : formatti
  iapp : formatti → formatti → formatti

bitstr : Set
bitstr = 𝕃 𝔹

data formati : formatti → Set where
   flit : 𝔹 → formati inone
   farg : formati iarg
   fapp : {a b : formatti} → formati a → formati b → formati (iapp a b)
   flet : {a b : formatti} → formati a → (formati inone → formati b) → formati (iapp a b)
   fbitstr : bitstr → formati inone

format-th : formatti → Set → Set
format-th iarg r = 𝔹 → r
format-th inone r = r
format-th (iapp i i') r = format-th i (format-th i' r)

format-t : formatti → Set
format-t i = format-th i bitstr

formath : {i : formatti} → formati i → {A : Set} → (bitstr → A) → format-th i A
formath (flit x) f = f [ x ]
formath farg f x = f [ x ]
formath (fapp i i') f = formath i (λ s → formath i' λ s' → f (s ++ s'))
formath (flet i i') f = formath i (λ s → formath (i' (fbitstr s)) f)
formath (fbitstr s) f = f s

format : {i : formatti} → formati i → format-t i
format i = formath i (λ x → x) 

test1i : formatti
test1i = iapp inone (iapp iarg inone)

test1 : formati test1i
test1 = (fapp (flit tt) (fapp farg (flit ff)))

test1-format-t : Set
test1-format-t = format-t test1i

test1-format : format-t test1i
test1-format = format test1

test2i : formatti
test2i = iapp inone (iapp (iapp iarg (iapp inone (iapp iarg inone))) (iapp inone inone))

test2 : formati test2i
test2 = (fapp (flit tt) (flet (fapp farg (fapp (flit ff) (fapp farg (fbitstr [])))) (λ i → fapp i i)))

test2-format-t : Set
test2-format-t = format-t test2i

test2-format : format-t test2i
test2-format = format test2