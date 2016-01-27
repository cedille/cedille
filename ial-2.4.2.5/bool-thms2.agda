module bool-thms2 where

open import bool
open import eq
open import product
open import sum

ff-imp : ∀ (b : 𝔹) → ff imp b ≡ tt
ff-imp ff = refl
ff-imp tt = refl

imp-tt : ∀ (b : 𝔹) → b imp tt ≡ tt
imp-tt ff = refl
imp-tt tt = refl

imp-ff : ∀ (b : 𝔹) → b imp ff ≡ ~ b
imp-ff tt = refl
imp-ff ff = refl

tt-imp : ∀ (b : 𝔹) → tt imp b ≡ b
tt-imp tt = refl
tt-imp ff = refl

&&-tt : ∀ (b : 𝔹) → b && tt ≡ b
&&-tt tt = refl
&&-tt ff = refl

||-ff : ∀ (b : 𝔹) → b || ff ≡ b
||-ff tt = refl
||-ff ff = refl

&&-contra : ∀ (b : 𝔹) → b && ~ b ≡ ff
&&-contra ff = refl
&&-contra tt = refl

&&-comm : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ b2 && b1
&&-comm ff ff = refl
&&-comm ff tt = refl
&&-comm tt ff = refl
&&-comm tt tt = refl

||-comm : ∀ (b1 b2 : 𝔹) → b1 || b2 ≡ b2 || b1
||-comm ff ff = refl
||-comm ff tt = refl
||-comm tt ff = refl
||-comm tt tt = refl

&&-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 && (b2 && b3) ≡ (b1 && b2) && b3
&&-assoc ff _ _ = refl
&&-assoc tt _ _ = refl

||-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 || (b2 || b3) ≡ (b1 || b2) || b3
||-assoc tt _ _ = refl
||-assoc ff _ _ = refl

~-over-&& : ∀ (b1 b2 : 𝔹) → ~ ( b1 && b2 ) ≡ (~ b1 || ~ b2)
~-over-&& tt _ = refl
~-over-&& ff _ = refl

~-over-|| : ∀ (b1 b2 : 𝔹) → ~ ( b1 || b2 ) ≡ (~ b1 && ~ b2)
~-over-|| tt _ = refl
~-over-|| ff _ = refl

&&-over-||-l : ∀ (a b c : 𝔹) → a && (b || c) ≡ (a && b) || (a && c)
&&-over-||-l tt _ _ = refl
&&-over-||-l ff _ _ = refl 

&&-over-||-r : ∀ (a b c : 𝔹) → (a || b) && c ≡ (a && c) || (b && c)
&&-over-||-r tt tt tt = refl
&&-over-||-r tt tt ff = refl
&&-over-||-r tt ff tt = refl
&&-over-||-r tt ff ff = refl
&&-over-||-r ff tt tt = refl
&&-over-||-r ff tt ff = refl
&&-over-||-r ff ff tt = refl
&&-over-||-r ff ff ff = refl

||-over-&&-l : ∀ (a b c : 𝔹) → a || (b && c) ≡ (a || b) && (a || c)
||-over-&&-l tt _ _ = refl
||-over-&&-l ff _ _ = refl 

||-over-&&-r : ∀ (a b c : 𝔹) → (a && b) || c ≡ (a || c) && (b || c)
||-over-&&-r tt _ _ = refl
||-over-&&-r ff _ ff = refl
||-over-&&-r ff tt tt = refl
||-over-&&-r ff ff tt = refl

&&-cong₁ : ∀ {b1 b1' b2 : 𝔹} → b1 ≡ b1' → b1 && b2 ≡ b1' && b2
&&-cong₁ refl = refl

&&-cong₂ : ∀ {b1 b2 b2' : 𝔹} → b2 ≡ b2' → b1 && b2 ≡ b1 && b2'
&&-cong₂ refl = refl 

&&-intro : ∀ {b1 b2 : 𝔹} → b1 ≡ tt → b2 ≡ tt → b1 && b2 ≡ tt
&&-intro{tt}{tt} _ _ = refl
&&-intro{tt}{ff} _ ()
&&-intro{ff}{tt} () _
&&-intro{ff}{ff} () _

||-intro1 : ∀ {b1 b2 : 𝔹} → b1 ≡ tt → b1 || b2 ≡ tt
||-intro1 {tt} p = refl
||-intro1 {ff} ()

&&-elim : ∀ {b1 b2 : 𝔹} → b1 && b2 ≡ tt → b1 ≡ tt ∧ b2 ≡ tt 
&&-elim{tt}{tt} _ = refl , refl
&&-elim{ff}{_} ()
&&-elim{tt}{ff} ()

&&-elim1 : ∀ {b1 b2 : 𝔹} → b1 && b2 ≡ tt → b1 ≡ tt
&&-elim1 p with &&-elim p
&&-elim1 _ | p , _ = p

&&-elim2 : ∀ {b1 b2 : 𝔹} → b1 && b2 ≡ tt → b2 ≡ tt
&&-elim2{b1} p with &&-elim{b1} p
&&-elim2 _ | _ , p = p

||-elim : ∀ {b1 b2 : 𝔹} → b1 || b2 ≡ tt → b1 ≡ tt ∨ b2 ≡ tt
||-elim {tt} refl = inj₁ refl
||-elim {ff} refl = inj₂ refl

~-cong : ∀ {b b' : 𝔹} → b ≡ b' → ~ b ≡ ~ b'
~-cong refl = refl

ite-cong₁ : ∀{ℓ}{A : Set ℓ} {b b' : 𝔹}(x y : A) → b ≡ b' → (if b then x else y) ≡ (if b' then x else y)
ite-cong₁ x y refl = refl

ite-cong₂ : ∀{ℓ}{A : Set ℓ} (b : 𝔹){x x' : A}(y : A) → x ≡ x' → (if b then x else y) ≡ (if b then x' else y)
ite-cong₂ b y refl = refl

ite-cong₃ : ∀{ℓ}{A : Set ℓ} (b : 𝔹)(x : A){y y' : A} → y ≡ y' → (if b then x else y) ≡ (if b then x else y')
ite-cong₃ b x refl = refl

&&-split : ∀ {b b' : 𝔹} → b || b' ≡ ff → b ≡ ff ⊎ b' ≡ ff
&&-split {tt} ()
&&-split {ff}{tt} ()
&&-split {ff}{ff} p = inj₁ refl

-----------------------------------
-- Theorems about imp
-----------------------------------
imp-same : ∀ (b : 𝔹) → b imp b ≡ tt
imp-same ff = refl
imp-same tt = refl

imp-to-|| : ∀ (b1 b2 : 𝔹) → (b1 imp b2) ≡ (~ b1 || b2)
imp-to-|| ff _ = refl
imp-to-|| tt _ = refl

imp-mp : ∀ {b b' : 𝔹} → b imp b' ≡ tt → b ≡ tt → b' ≡ tt 
imp-mp {tt} {tt} p refl = refl
imp-mp {ff} {ff} p q = q
imp-mp {tt} {ff} p q = p
imp-mp {ff} {tt} p q = refl

imp-antisymm : ∀ {b1 b2 : 𝔹} → b1 imp b2 ≡ tt → b2 imp b1 ≡ tt → b1 ≡ b2
imp-antisymm{tt}{tt} p q = refl
imp-antisymm{tt}{ff} () q 
imp-antisymm{ff}{tt} p ()
imp-antisymm{ff}{ff} p q = refl

-----------------------------------
-- Theorems about xor
-----------------------------------
ff-xor : ∀ (b : 𝔹) → ff xor b ≡ b
ff-xor tt = refl
ff-xor ff = refl

tt-xor : ∀ (b : 𝔹) → tt xor b ≡ ~ b
tt-xor tt = refl
tt-xor ff = refl

~-xor-distrb : ∀ (a b : 𝔹) → ~ (a xor b) ≡ ~ a xor b
~-xor-distrb tt tt = refl
~-xor-distrb tt ff = refl
~-xor-distrb ff tt = refl
~-xor-distrb ff ff = refl

xor-distrib-&& : ∀ (x y : 𝔹) → x xor (y && x) ≡ ~ y && x
xor-distrib-&& tt tt = refl
xor-distrib-&& tt ff = refl
xor-distrib-&& ff tt = refl
xor-distrib-&& ff ff = refl

xor~hop : ∀ (a b : 𝔹) → ~ a xor b ≡ a xor ~ b
xor~hop tt tt = refl
xor~hop tt ff = refl
xor~hop ff tt = refl
xor~hop ff ff = refl

xor-comm : ∀ (b1 b2 : 𝔹) → b1 xor b2 ≡ b2 xor b1
xor-comm tt tt = refl
xor-comm tt ff = refl
xor-comm ff tt = refl
xor-comm ff ff = refl

xor-assoc : (b1 b2 b3 : 𝔹) → b1 xor (b2 xor b3) ≡ (b1 xor b2) xor b3
xor-assoc tt tt tt = refl
xor-assoc tt tt ff = refl
xor-assoc tt ff tt = refl
xor-assoc tt ff ff = refl
xor-assoc ff tt tt = refl
xor-assoc ff tt ff = refl
xor-assoc ff ff tt = refl
xor-assoc ff ff ff = refl

xor-anti-idem : (b : 𝔹) → b xor b ≡ ff
xor-anti-idem tt = refl
xor-anti-idem ff = refl

xor-≡ : {b1 b2 : 𝔹} → b1 xor b2 ≡ ff → b1 ≡ b2
xor-≡ {tt} {tt} p = refl
xor-≡ {tt} {ff} ()
xor-≡ {ff} {tt} ()
xor-≡ {ff} {ff} p = refl

-----------------------------------
-- Theorems about nor, nand
-----------------------------------

nor-not : ∀ (b : 𝔹) → b nor b ≡ ~ b
nor-not tt = refl
nor-not ff = refl

nor-or : ∀ (b1 b2 : 𝔹) → (b1 nor b2) nor (b1 nor b2) ≡ b1 || b2
nor-or tt b2 = refl
nor-or ff tt = refl
nor-or ff ff = refl

nor-and : ∀ (b1 b2 : 𝔹) → (b1 nor b1) nor (b2 nor b2) ≡ b1 && b2
nor-and tt tt = refl
nor-and tt ff = refl
nor-and ff b2 = refl

nor-comm : ∀ (b1 b2 : 𝔹) → b1 nor b2 ≡ b2 nor b1
nor-comm tt tt = refl
nor-comm tt ff = refl
nor-comm ff tt = refl
nor-comm ff ff = refl

nand-comm : ∀ (b1 b2 : 𝔹) → b1 nand b2 ≡ b2 nand b1
nand-comm tt tt = refl
nand-comm tt ff = refl
nand-comm ff tt = refl
nand-comm ff ff = refl

