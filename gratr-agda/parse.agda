open import parse-tree
open import lib

module parse (gratr2-nt : Set)(ptr : ParseTreeRec) where

open import rtn gratr2-nt

open import run ptr

module pderiv (rrs : deriv.rewriteRules)(x : gratr2-rtn) where
  open deriv 
  open rewriteRules rrs
  open gratr2-rtn x


----------------------------------------------------------------------
-- code to run the automaton on a list of characters
----------------------------------------------------------------------

  data RE : Set where
    ic : char → RE
    rulename : string → RE

  re-to-run : (run : 𝕃 RE) → (rc : 𝕃 char) → Run rc
  re-to-run ((ic c) :: res) (rc :: rcs) = InputChar rc ::' re-to-run res rcs
  re-to-run (rulename s :: res) rcs = Id s ::' re-to-run res rcs
  re-to-run [] [] = []'
  re-to-run run (rc :: rcs) = InputChar rc ::' re-to-run run rcs
  re-to-run run [] = []'

  insert-front-id : gratr2-rule → 𝕃 RE → 𝕃 RE
  insert-front-id (just id , _ ) run = rulename id :: run
  insert-front-id _ run = run

  insert-back-id : maybe string → 𝕃 RE → 𝕃 RE
  insert-back-id (just id) run = rulename id :: run
  insert-back-id _ run = run

  {-# TERMINATING #-}
  parse : (inputchars : 𝕃 char) → (least : 𝕃 char) → (run : 𝕃 RE) → (frames : 𝕃 (gratr2-rule)) → (continuation : 𝕃 char → 𝕃 char ⊎ 𝕃 RE) → 𝕃 char ⊎ 𝕃 RE 
  parse-filter : (inputchars : 𝕃 char) → (least : 𝕃 char) → (run : 𝕃 RE) → (frames : 𝕃 gratr2-rule) → (candidateframes : 𝕃 gratr2-rule) → (continuation : 𝕃 char → 𝕃 char ⊎ 𝕃 RE) → 𝕃 char ⊎ 𝕃 RE
  
  parse-filter cs least run frames [] contin = contin (if least longer cs then cs else least)
  parse-filter cs least run frames (r :: rs) contin = parse cs least (insert-front-id r run) (r :: frames) (\ least → parse-filter cs least run frames rs contin)

  parse [] _ run [] contin = inj₂ run
  parse [] _ run ((id , id' , orig , inj₁ nt :: rule) :: rest) contin = parse-filter [] [] run ((id , id' , orig , rule) :: rest) (gratr2-start nt) contin
  parse [] _ run ((_ , _ , _ , inj₂ c :: rule) :: rest) contin = contin []
  parse [] _ run ((_ , id , _) :: rest) contin = parse [] [] (insert-back-id id run) rest contin

  
  parse (c :: cs) least run [] contin = contin (c :: cs)
  parse (c :: cs) least run ((id , id' , nothing , inj₁ nt :: rule) :: rest) contin = parse-filter (c :: cs) least run ((id , id' , nothing , rule) :: rest) (gratr2-start nt) contin
  parse (c :: cs) least run ((id , id' , just orig , inj₁ nt :: rule) :: rest) contin with length rule =ℕ 0 && nt eq orig | id'
  ...| ff | _ = parse-filter (c :: cs) least run ((id , id' , just orig , rule) :: rest) (gratr2-start nt) contin
  ...| tt | nothing = parse-filter (c :: cs) least run rest (gratr2-start nt) contin 
  ...| tt | just x = parse-filter (c :: cs) least run ((id , id' , nothing , rule) :: rest) (gratr2-start nt) contin 
  parse (c :: cs) least run ((id , id' , orig , inj₂ c' :: rule) :: rest) contin with c =char c'
  ...| tt = parse cs least (ic c :: run) ((id , id' , orig , rule) :: rest) contin
  ...| ff = contin (if least longer (c :: cs) then c :: cs else least)
  parse (c :: cs) least run ((_ , id , orig , []) :: rest) contin = parse-filter (c :: cs) least (insert-back-id id run) rest (gratr2-return orig) (\ least → parse (c :: cs) least (insert-back-id id run) rest contin)

  runRtn : (lc : 𝕃 char) → 𝕃 char ⊎ Run lc
  runRtn lc with parse-filter lc lc [] [] (gratr2-start start) inj₁ 
  ...| inj₁ left = inj₁ left
  ...| inj₂ run = inj₂ (re-to-run (reverse run) lc)


---------------------------------------------------------------------
-- code to apply run-rewriting rules to a run
----------------------------------------------------------------------

  {-# TERMINATING #-}
  rewrite-main : {lc : 𝕃 char} → ℕ → (r : Run lc) → (𝔹 × ℕ × Run lc)
  rewrite-main _ []' = (ff , 1 , []')
  rewrite-main 0 (e ::' r) = (ff , 1 , e ::' r)
  rewrite-main (suc n) (e ::' r) with rewrite-main n r 
  ... | (b , n' , r') with len-dec-rewrite (e ::' r') 
  ... | nothing = (b , (if b then suc n' else 1) , e ::' r') 
  ... | just (r'' , k) with n' ∸ k 
  ... | 0 = rewrite-main 1 r''
  ... | n'' = rewrite-main  n'' r''


  rewriteRun : {lc : 𝕃 char} → Run lc → Run lc
  rewriteRun r with rewrite-main (length-run r) r
  ...| (_ , _ , r') = r'

module pnoderiv (rrs : noderiv.rewriteRules)(x : gratr2-rtn) where
  open noderiv 
  open rewriteRules rrs
  open gratr2-rtn x

----------------------------------------------------------------------
-- code to run the automaton on a list of characters
----------------------------------------------------------------------

  data RE : Set where
    ic : char → RE
    rulename : string → RE

  re-to-run : ℕ → (run : 𝕃 RE) → Run 
  re-to-run n ((ic c) :: res) = InputChar c ::' re-to-run (suc n) res 
  re-to-run n (rulename "Posinfo" :: res) = Posinfo n ::' re-to-run n res 
  re-to-run n (rulename s :: res) = Id s ::' re-to-run n res 
  re-to-run _ [] = []'

  insert-front-id : gratr2-rule → 𝕃 RE → 𝕃 RE
  insert-front-id (just id , _ ) run = rulename id :: run
  insert-front-id _ run = run

  insert-back-id : maybe string → 𝕃 RE → 𝕃 RE
  insert-back-id (just id) run = rulename id :: run
  insert-back-id _ run = run

  {-# TERMINATING #-}
  parse : (inputchars : 𝕃 char) → (least : 𝕃 char) → (run : 𝕃 RE) → (frames : 𝕃 (gratr2-rule)) → (continuation : 𝕃 char → 𝕃 char ⊎ 𝕃 RE) → 𝕃 char ⊎ 𝕃 RE 
  parse-filter : (inputchars : 𝕃 char) → (least : 𝕃 char) → (run : 𝕃 RE) → (framse : 𝕃 gratr2-rule) → (candidateframes : 𝕃 gratr2-rule) → (continuation : 𝕃 char → 𝕃 char ⊎ 𝕃 RE) → 𝕃 char ⊎ 𝕃 RE
  
  parse-filter cs least run frames [] contin = contin (if least longer cs then cs else least)
  parse-filter cs least run frames (r :: rs) contin = parse cs least (insert-front-id r run) (r :: frames) (\ least → parse-filter cs least run frames rs contin)

  parse [] _ run [] contin = inj₂ run
  parse [] _ run ((id , id' , orig , inj₁ nt :: rule) :: rest) contin = parse-filter [] [] run ((id , id' , orig , rule) :: rest) (gratr2-start nt) contin
  parse [] _ run ((_ , _ , _ , inj₂ c :: rule) :: rest) contin = contin []
  parse [] _ run ((_ , id , _) :: rest) contin = parse [] [] (insert-back-id id run) rest contin

  parse (c :: cs) least run [] contin = contin (c :: cs)
  parse (c :: cs) least run ((id , id' , nothing , inj₁ nt :: rule) :: rest) contin = parse-filter (c :: cs) least run ((id , id' , nothing , rule) :: rest) (gratr2-start nt) contin
  parse (c :: cs) least run ((id , id' , just orig , inj₁ nt :: rule) :: rest) contin with length rule =ℕ 0 && nt eq orig | id'
  ...| ff | _ = parse-filter (c :: cs) least run ((id , id' , just orig , rule) :: rest) (gratr2-start nt) contin
  ...| tt | nothing = parse-filter (c :: cs) least run rest (gratr2-start nt) contin 
  ...| tt | just x = parse-filter (c :: cs) least run ((id , id' , nothing , rule) :: rest) (gratr2-start nt) contin 
  parse (c :: cs) least run ((id , id' , orig , inj₂ c' :: rule) :: rest) contin with c =char c'
  ...| tt = parse cs least (ic c :: run) ((id , id' , orig , rule) :: rest) contin
  ...| ff = contin (if least longer (c :: cs) then c :: cs else least)
  parse (c :: cs) least run ((_ , id , orig , []) :: rest) contin = parse-filter (c :: cs) least (insert-back-id id run) rest (gratr2-return orig) (\ least → parse (c :: cs) least (insert-back-id id run) rest contin)

  runRtn : (lc : 𝕃 char) → 𝕃 char ⊎ Run 
  runRtn lc with parse-filter lc lc [] [] (gratr2-start start) inj₁
  ...| inj₁ left = inj₁ left
  ...| inj₂ run = inj₂ (re-to-run 1 (reverse run))


---------------------------------------------------------------------
-- code to apply run-rewriting rules to a run
----------------------------------------------------------------------

  {-# TERMINATING #-}
  rewrite-main : ℕ → Run → (𝔹 × ℕ × Run)
  rewrite-main _ [] = (ff , 1 , []')
  rewrite-main 0 (e :: r) = (ff , 1 , e ::' r)
  rewrite-main (suc n) (e :: r) with rewrite-main n r 
  ... | (b , n' , r') with len-dec-rewrite (e ::' r') 
  ... | nothing = (b , (if b then suc n' else 1) , e ::' r') 
  ... | just (r'' , k) with n' ∸ k 
  ... | 0 = rewrite-main 1 r''
  ... | n'' = rewrite-main  n'' r''


  rewriteRun : Run → Run
  rewriteRun r with rewrite-main (length-run r) r
  ...| (_ , _ , r') = r'


