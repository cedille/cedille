module nat-log-test where

open import eq
open import nat
open import nat-log

test : log-result 11 3
test = log 11 3 refl refl

exp-from-test : ℕ
exp-from-test with test
exp-from-test | pos-power e s p = e
exp-from-test | no-power p = 0
