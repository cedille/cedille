module bohm-out where
open import lib
open import general-util
open import cedille-types
open import syntax-util

{- Implementation of the Böhm-Out Algorithm -}

private
  
  nfoldr : ℕ → ∀ {ℓ} {X : Set ℓ} → X → (ℕ → X → X) → X
  nfoldr zero    z s = z
  nfoldr (suc n) z s = s n (nfoldr n z s)
  
  nfoldl : ℕ → ∀ {ℓ} {X : Set ℓ} → X → (ℕ → X → X) → X
  nfoldl zero    z s = z
  nfoldl (suc n) z s = nfoldl n (s n z) s
  
  set-nth : ∀ {ℓ} {X : Set ℓ} → ℕ → X → 𝕃 X → 𝕃 X
  set-nth n x [] = []
  set-nth zero x (x' :: xs) = x :: xs
  set-nth (suc n) x (x' :: xs) = x' :: set-nth n x xs
  
  
  
  -- Böhm Tree
  data BT : Set where
    Node : (n i : ℕ) → 𝕃 BT → BT
  -- n: number of lambdas currently bound
  -- i: head variable
  -- 𝕃 BT: list of arguments
  
  -- Path to difference
  data path : Set where
    hd : path                  -- Difference in heads
    as : path                  -- Difference in number of arguments
    ps : (n : ℕ) → path → path -- Difference in nth subtrees (recursive)
  
  
  
  -- η functions
  η-expand'' : ℕ → 𝕃 BT → 𝕃 BT
  η-expand'' g [] = []
  η-expand'' g (Node n i b :: bs) =
    Node (suc n) (if i ≥ g then suc i else i) (η-expand'' g b) :: η-expand'' g bs
  
  η-expand' : ℕ → BT → BT
  η-expand' g (Node n i b) = Node (suc n) (if i ≥ g then suc i else i) (η-expand'' g b)
  
  η-expand : BT → BT
  η-expand t @ (Node n _ _) with η-expand' (suc n) t
  ...| Node n' i' b' = Node n' i' (b' ++ [ Node n' n' [] ])
  
  bt-n : BT → ℕ
  bt-n (Node n i b) = n
  
  η-equate : BT → BT → BT × BT
  η-equate t₁ t₂ =
    nfoldr (bt-n t₂ ∸ bt-n t₁) t₁ (λ _ → η-expand) ,
    nfoldr (bt-n t₁ ∸ bt-n t₂) t₂ (λ _ → η-expand)
  
  -- η-equates all nodes along path to difference
  η-equate-path : BT → BT → path → BT × BT
  η-equate-path (Node n₁ i₁ b₁) (Node n₂ i₂ b₂) (ps d p) =
    let b-b = h d b₁ b₂ in
    η-equate (Node n₁ i₁ (fst b-b)) (Node n₂ i₂ (snd b-b))
    where
    h : ℕ → 𝕃 BT → 𝕃 BT → 𝕃 BT × 𝕃 BT
    h zero (b₁ :: bs₁) (b₂ :: bs₂) with η-equate-path b₁ b₂ p
    ...| b₁' , b₂' = b₁' :: bs₁ , b₂' :: bs₂
    h (suc d) (b₁ :: bs₁) (b₂ :: bs₂) with h d bs₁ bs₂
    ...| bs₁' , bs₂' = b₁ :: bs₁' , b₂ :: bs₂'
    h d b₁ b₂ = b₁ , b₂
  η-equate-path t₁ t₂ p = η-equate t₁ t₂
  
  
  
  -- Rotation functions
  rotate : (k : ℕ) → BT
  rotate k =
    Node (suc k) (suc k) (nfoldl k [] (λ k' → Node (suc k) (suc k') [] ::_))
  
  rotate-BT' : ℕ → 𝕃 BT → 𝕃 BT
  rotate-BT' k [] = []
  rotate-BT' k (Node n i b :: bs) with i =ℕ k
  ...| ff = Node n i (rotate-BT' k b) :: rotate-BT' k bs
  ...| tt = Node (suc n) (suc n) (η-expand'' (suc n) (rotate-BT' k b)) :: rotate-BT' k bs
  rotate-BT : ℕ → BT → BT
  rotate-BT k (Node n i b) with i =ℕ k
  ...| ff = Node n i (rotate-BT' k b)
  ...| tt = Node (suc n) (suc n) (η-expand'' (suc n) (rotate-BT' k b))
  
  -- Returns the greatest number of arguments k ever has at each node it where it is the head
  greatest-apps' : ℕ → 𝕃 BT → ℕ
  greatest-apps' k [] = zero
  greatest-apps' k (Node n k' bs' :: bs) with k =ℕ k'
  ...| ff = max (greatest-apps' k bs') (greatest-apps' k bs)
  ...| tt = max (length bs') (max (greatest-apps' k bs') (greatest-apps' k bs))
  greatest-apps : ℕ → BT → ℕ
  greatest-apps k (Node n i b) with k =ℕ i
  ...| ff = greatest-apps' k b
  ...| tt = max (length b) (greatest-apps' k b)
  greatest-η' : ℕ → ℕ → 𝕃 BT → 𝕃 BT
  greatest-η' k m [] = []
  greatest-η' k m (Node n i bs :: bs') with k =ℕ i
  ...| ff = Node n i (greatest-η' k m bs) :: greatest-η' k m bs'
  ...| tt = nfoldr (m ∸ length bs) (Node n i (greatest-η' k m bs)) (λ _ → η-expand) :: greatest-η' k m bs'
  greatest-η : ℕ → ℕ → BT → BT
  greatest-η k m (Node n i b) with k =ℕ i
  ...| ff = Node n i (greatest-η' k m b)
  ...| tt = nfoldr (m ∸ length b) (Node n i (greatest-η' k m b)) (λ _ → η-expand)
  
  -- Returns tt if k ever is at the head of a node along the path to the difference
  occurs-in-path : ℕ → BT → path → 𝔹
  occurs-in-path k (Node n i b) (ps d p) =
    k =ℕ i || maybe-else ff (λ t → occurs-in-path k t p) (nth d b)
  occurs-in-path k (Node n i b) p = k =ℕ i

  adjust-path : ℕ → BT → path → path
  adjust-path k (Node n i b) (ps d p) = maybe-else' (nth d b) (ps d p) λ n → ps d (adjust-path k n p)
  adjust-path k (Node n i b) as with k =ℕ i
  ...| tt = hd
  ...| ff = as
  adjust-path k (Node n i b) hd = hd
  
  
  
  -- Δ functions
  construct-BT : term → maybe BT
  construct-BT = h zero empty-trie Node where
    h : ℕ → trie ℕ → ((n i : ℕ) → 𝕃 BT → BT) → term → maybe BT
    h n vm f (Var _ x) = just (f n (trie-lookup-else zero vm x) [])
    h n vm f (App t NotErased t') =
      h n vm Node t' ≫=maybe λ t' →
      h n vm (λ n i b → f n i (b ++ [ t' ])) t
    h n vm f (Lam _ NotErased _ x NoClass t) = h (suc n) (trie-insert vm x (suc n)) f t
    h n vm f t = nothing
  
  {-# TERMINATING #-}
  construct-path' : BT → BT → maybe (path × BT × BT)
  construct-path : BT → BT → maybe (path × BT × BT)
  construct-path (Node _ zero _) _ = nothing
  construct-path _ (Node _ zero _) = nothing
  construct-path t₁ t₂ = uncurry construct-path' (η-equate t₁ t₂)
  construct-path' t₁ @ (Node n₁ i₁ b₁) t₂ @ (Node n₂ i₂ b₂) =
    if ~ i₁ =ℕ i₂
      then just (hd , t₁ , t₂)
      else if length b₁ =ℕ length b₂
        then maybe-map (λ {(p , b₁ , b₂) → p , Node n₁ i₁ b₁ , Node n₂ i₂ b₂}) (h zero b₁ b₂)
        else just (as , t₁ , t₂)
    where
    h : ℕ → 𝕃 BT → 𝕃 BT → maybe (path × 𝕃 BT × 𝕃 BT)
    h n (b₁ :: bs₁) (b₂ :: bs₂) =
      maybe-else
        (maybe-map (λ {(p , bs₁ , bs₂) → p , b₁ :: bs₁ , b₂ :: bs₂}) (h (suc n) bs₁ bs₂))
        (λ {(p , b₁ , b₂) → just (ps n p , b₁ :: bs₁ , b₂ :: bs₂)})
        (construct-path b₁ b₂)
    h _ _ _ = nothing
  
  {-# TERMINATING #-}
  construct-Δ : BT → BT → path → 𝕃 BT
  construct-Δ (Node n₁ i₁ b₁) (Node n₂ i₂ b₂) hd =
    nfoldl n₁ [] λ m → _::_
      (if suc m =ℕ i₁
        then Node (2 + length b₁) (1 + length b₁) []
        else if suc m =ℕ i₂
          then Node (2 + length b₂) (2 + length b₂) []
          else Node 1 1 [])
  construct-Δ (Node n₁ i₁ b₁) (Node n₂ i₂ b₂) as =
    let l₁ = length b₁
        l₂ = length b₂
        d = l₁ > l₂
        lM = if d then l₁ else l₂
        lm = if d then l₂ else l₁
        l = lM ∸ lm in
    nfoldl n₁
      (nfoldr l [ Node (2 + l) ((if d then 1 else 2) + l) [] ]
         λ l' → _++
           [ if suc l' =ℕ l
               then Node 2 (if d then 2 else 1) []
               else Node 1 1 [] ])
     (λ n' → _::_
       (if suc n' =ℕ i₁
         then Node (suc lM) (suc lM) []
         else Node 1 1 []))
  construct-Δ t₁ @ (Node n₁ i₁ b₁) t₂ @ (Node n₂ i₂ b₂) (ps d p)
    with nth d b₁ ≫=maybe λ b₁ → nth d b₂ ≫=maybe λ b₂ → just (b₁ , b₂)
  ...| nothing = [] -- Shouldn't happen
  ...| just (t₁' @ (Node n₁' i₁' b₁') , t₂' @ (Node n₂' i₂' b₂'))
    with occurs-in-path i₁ t₁' p || occurs-in-path i₂ t₂' p
  ...| ff = set-nth (pred i₁) (Node (length b₁) (suc d) []) (construct-Δ t₁' t₂' p)
  ...| tt with max (greatest-apps i₁ t₁) (greatest-apps i₂ t₂)
  ...| kₘ with η-equate-path (rotate-BT i₁ (greatest-η i₁ kₘ t₁))
                             (rotate-BT i₂ (greatest-η i₂ kₘ t₂)) (ps d p)
  ...| t₁'' , t₂'' = set-nth (pred i₁) (rotate kₘ) (construct-Δ t₁'' t₂'' (ps d $ adjust-path i₁ t₁' p))
  
  reconstruct : BT → term
  reconstruct = h zero where
    mkvar : ℕ → var
    mkvar n = "x" ^ ℕ-to-string n
    h : ℕ → BT → term
    a : ℕ → term → 𝕃 BT → term
    a n t [] = t
    a n t (b :: bs) = a n (mapp t (h n b)) bs
    h m (Node n i b) = nfoldl (n ∸ m) (a n (mvar (mkvar i)) b) (λ nm → mlam (mkvar (suc (m + nm))))
  
-- Returns a term f such that f t₁ ≃ λ t. λ f. t and f t₂ ≃ λ t. λ f. f, assuming two things:
-- 1. t₁ ≄ t₂
-- 2. The head of each node along the path to the difference between t₁ and t₂ is bound
--    withing the terms (so λ x. λ y. y y (x y) and λ x. λ y. y y (x x) works, but not
--    λ x. λ y. y y (f y), where f is already declared/defined)
make-contradiction : (t₁ t₂ : term) → maybe term
make-contradiction t₁ t₂ =
  construct-BT t₁ ≫=maybe λ t₁ →
  construct-BT t₂ ≫=maybe λ t₂ →
  construct-path t₁ t₂ ≫=maybe λ {(p , t₁ , t₂) →
  just (reconstruct (Node (suc zero) (suc zero)
    (map (η-expand' zero) (construct-Δ t₁ t₂ p))))}

-- Returns tt if the two terms are provably not equal
is-contradiction : term → term → 𝔹
is-contradiction t₁ t₂ = isJust (make-contradiction t₁ t₂)

