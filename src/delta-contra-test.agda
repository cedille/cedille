module delta-contra-test where
open import cedille-options
open import cedille-types
open import ctxt
open import lib
open import rename
open import syntax-util
open import to-string default-options
open import general-util

nlam : ℕ → term → term
nlam 0 t = t
nlam (suc n) t = mlam "_" (nlam n t)

elab-contra-app : ℕ → (ℕ → term) → term
elab-contra-app 0 nt = mvar "x"
elab-contra-app (suc n) nt = mapp (elab-contra-app n nt) (nt n)

elab-contrahh : ℕ → trie ℕ → trie ℕ → var → var → 𝕃 term → 𝕃 term → maybe term
elab-contrahh n ls rs x1 x2 as1 as2 with trie-lookup ls x1 | trie-lookup rs x2
...| just n1 | just n2 =
  let t1 = nlam (length as1) (mlam "x" (mlam "y" (mvar "x")))
      t2 = nlam (length as2) (mlam "x" (mlam "y" (mvar "y"))) in
  if n1 =ℕ n2
    then nothing
    else just (mlam "x" (elab-contra-app n
      (λ n → if n =ℕ n1 then t1 else if n =ℕ n2 then t2 else id-term)))
...| _ | _ = nothing

{-# TERMINATING #-}
elab-contrah : ℕ → trie ℕ → trie ℕ → term → term → maybe term
elab-contrah n ls rs (Lam _ _ _ x1 _ t1) (Lam _ _ _ x2 _ t2) =
  elab-contrah (suc n) (trie-insert ls x1 n) (trie-insert rs x2 n) t1 t2
elab-contrah n ls rs (Lam _ _ _ x1 _ t1) t2 =
  elab-contrah (suc n) (trie-insert ls x1 n) (trie-insert rs x1 n) t1 (mapp t2 (mvar x1))
elab-contrah n ls rs t1 (Lam _ _ _ x2 _ t2) =
  elab-contrah (suc n) (trie-insert ls x2 n) (trie-insert rs x2 n) (mapp t1 (mvar x2)) t2
elab-contrah n ls rs t1 t2 with decompose-apps t1 | decompose-apps t2
...| Var _ x1 , as1 | Var _ x2 , as2 = elab-contrahh n ls rs x1 x2 as1 as2
...| _ | _ = nothing

-- For terms t1 and t2, given that check-beta-inequiv t1 t2 is tt,
-- elab-contra produces a function f such that f t1 ≡ tt and f t2 ≡ ff
elab-contra : term → term → maybe term
elab-contra = elab-contrah 0 empty-trie empty-trie
-- postulate: check-beta-inequiv t1 t2 ≡ isJust (elab-contra t1 t2)

{- Tests -}
to-contra : term → term → string
to-contra t1 t2 with elab-contra t1 t2
...| just f = rope-to-string (to-string empty-ctxt f)
...| nothing = "No contradiction could be found"

nat-contra = to-contra -- "λ x . x (λ x . λ y . x) (λ _ . λ x . λ y . y)"
  (mlam "z" (mlam "s" (mvar "z"))) -- λ z . λ s . z
  (mlam "z" (mlam "s" (mapp (mvar "s") (mapp (mapp (mvar "n") (mvar "z")) (mvar "s"))))) -- λ z . λ s . s (n z s)

bool-contra = to-contra -- λ x . x (λ x . λ y . x) (λ x . λ y . y)
  (mlam "t" (mlam "f" (mvar "t"))) -- λ t . λ f . t
  (mlam "t" (mlam "f" (mvar "f"))) -- λ t . λ f . f
  
maybe-contra = to-contra -- λ x . x (λ x . λ y . x) (λ _ . λ x . λ y . y)
  (mlam "n" (mlam "j" (mvar "n"))) -- λ n . λ j . n
  (mlam "n" (mlam "j" (mapp (mvar "j") (mvar "a")))) -- λ n . λ j . j a

-- Some more interesting examples
id-ff-contra = to-contra -- λ x . x (λ _ . λ x . λ y . x) (λ x . λ y . y)
  (mlam "x" (mvar "x")) -- λ x . x
  (mlam "t" (mlam "f" (mvar "f"))) -- λ t . λ f . f

xy-yx-contra = to-contra -- λ x . x (λ _ . λ x . λ y . x) (λ _ . λ x . λ y . y)
  (mlam "x" (mvar "x")) -- λ x . λ y . x y (eta-equal to λ x . x)
  (mlam "x" (mlam "y" (mapp (mvar "y") (mvar "x")))) -- λ x . λ y . y x
