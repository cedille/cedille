module subst where

open import lib

open import cedille-types
open import ctxt
open import syntax-util

term-subst-kind : ctxt → term → var → kind → kind
term-subst-kind Γ t x k = k
