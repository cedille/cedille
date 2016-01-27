module main where

import parse
open import lib
open import huffman-types
import huffman

module parsem = parse huffman.gratr2-nt ptr
open parsem
open parsem.pnoderiv huffman.rrs huffman.huffman-rtn
open import run ptr
open noderiv {- from run.agda -}

{- imports for Huffman trees and also 
   Braun trees specialized to store Huffman trees
   with lower frequency ones nearer the root -}
open import huffman-tree
import braun-tree as bt
open bt huffman-tree ht-compare

--open import braun-tree huffman-tree ht-compare

pqueue : ℕ → Set
pqueue = braun-tree

pq-empty : pqueue 0
pq-empty = bt-empty

pq-insert : ∀ {n : ℕ} → huffman-tree → pqueue n → pqueue (suc n)
pq-insert = bt-insert

pq-remove-min : ∀ {p : ℕ} → pqueue (suc p) → huffman-tree × pqueue p
pq-remove-min = bt-remove-min

data output-type : Set where
  encode-output : string → string → string → string → output-type
  decode-output : string → output-type
  error-output : string → output-type -- error message if there is an error

inc-frequency : word → trie ℕ → trie ℕ
inc-frequency w t with trie-lookup t w
inc-frequency w t | nothing = trie-insert t w 1
inc-frequency w t | just c = trie-insert t w (suc c)

compute-frequencies : words → trie ℕ → trie ℕ
compute-frequencies (WordsStart w) t = inc-frequency w t
compute-frequencies (WordsNext w ww) t = compute-frequencies ww (inc-frequency w t)

inc-frequency-nonempty : ∀(w : word)(t : trie ℕ) → trie-nonempty (inc-frequency w t) ≡ tt
inc-frequency-nonempty w t with trie-lookup t w
inc-frequency-nonempty w t | nothing = trie-insert-nonempty t w 1
inc-frequency-nonempty w t | just c = trie-insert-nonempty t w (suc c)

compute-frequencies-nonempty : ∀(ws : words)(t : trie ℕ) → trie-nonempty (compute-frequencies ws t) ≡ tt
compute-frequencies-nonempty (WordsNext w ww) t = compute-frequencies-nonempty ww (inc-frequency w t)
compute-frequencies-nonempty (WordsStart w) t = inc-frequency-nonempty w t

build-huffman-pqueue : (l : 𝕃 (string × ℕ)) → pqueue (length l)
build-huffman-pqueue [] = pq-empty
build-huffman-pqueue ((s , f) :: l) = pq-insert (ht-leaf s f) (build-huffman-pqueue l)

-- where we call this function, we have enough evidence to prove the Braun tree is nonempty 
process-huffman-pqueue : ∀{n} → n =ℕ 0 ≡ ff → pqueue n → huffman-tree
process-huffman-pqueue{0} () b
process-huffman-pqueue{suc n} _ t with pq-remove-min t 
process-huffman-pqueue{suc 0} _ t | h , _ = h
process-huffman-pqueue{suc (suc n)} _ _ | h , t with pq-remove-min t 
process-huffman-pqueue{suc (suc n)} _ _ | h , _ | h' , t =
  process-huffman-pqueue{suc n} refl (pq-insert (ht-node ((ht-frequency h) + (ht-frequency h')) h h') t)

build-mappingh : huffman-tree → trie string → 𝕃 char → trie string
build-mappingh (ht-leaf s _) m l = trie-insert m s (𝕃char-to-string (reverse l))
build-mappingh (ht-node _ h1 h2) m l = 
  build-mappingh h2 (build-mappingh h1 m ('0' :: l)) ('1' :: l)

build-mapping : huffman-tree → trie string
build-mapping h = build-mappingh h empty-trie []

encode-word : trie string → word → string 
encode-word t w with trie-lookup t w
encode-word t w | nothing = "error"
encode-word t w | just s = s

encode-words : trie string → words → string 
encode-words t (WordsNext w ww) = encode-word t w ^ encode-words t ww
encode-words t (WordsStart w) = encode-word t w 

data code-tree : Set where
  ct-empty : code-tree
  ct-leaf : string → code-tree
  ct-node : code-tree → code-tree → code-tree

flip-digit : digit → digit
flip-digit Zero = One
flip-digit One = Zero

sub-ct : digit → code-tree → code-tree
sub-ct _ ct-empty = ct-empty
sub-ct _ (ct-leaf _) = ct-empty
sub-ct Zero (ct-node t1 t2) = t1
sub-ct One (ct-node t1 t2) = t2

ct-node-digit : digit → code-tree → code-tree → code-tree
ct-node-digit Zero t1 t2 = ct-node t1 t2
ct-node-digit One t1 t2 = ct-node t2 t1

ct-insert : code-tree → code → code-tree
ct-insert t (Code s (BvlitStart d)) = 
  -- child d of the new tree is the new leaf, and the other child is the other subtree of t
  ct-node-digit d (ct-leaf s) (sub-ct (flip-digit d) t)
ct-insert t (Code s (BvlitCons d v)) = 
  -- child d of the new tree is obtained recursively and the other child is the other subtree of t
  ct-node-digit d (ct-insert (sub-ct d t) (Code s v)) (sub-ct (flip-digit d) t)

make-code-tree : code-tree → codes → code-tree
make-code-tree t (CodesNext c cs) = make-code-tree (ct-insert t c) cs
make-code-tree t (CodesStart c) = ct-insert t c

decode-stringh : code-tree → code-tree → bvlit → string 
decode-stringh orig n (BvlitCons d v) with sub-ct d n 
decode-stringh orig n (BvlitCons d v) | ct-leaf s = s ^ " " ^ (decode-stringh orig orig v)
decode-stringh orig n (BvlitCons d v) | ct-empty = "error\n"
decode-stringh orig n (BvlitCons d v) | n' = decode-stringh orig n' v
decode-stringh orig n (BvlitStart d) with sub-ct d n 
decode-stringh orig n (BvlitStart d) | ct-leaf s = s ^ "\n"
decode-stringh orig n (BvlitStart d) | _ = "error\n"

decode-string : code-tree → bvlit → string 
decode-string t v = decode-stringh t t v

process-cmd : cmd → output-type
process-cmd (Encode ww) = step (compute-frequencies ww empty-trie) (compute-frequencies-nonempty ww empty-trie) 
  where step : (t : trie ℕ) → trie-nonempty t ≡ tt → output-type
        step t nonempty-t =
         let s1 = trie-to-string " -> " ℕ-to-string t in
         let m = trie-mappings t in
         let wt = build-huffman-pqueue m in  
         let h = process-huffman-pqueue (is-empty-ff-length (trie-mappings t) (trie-mappings-nonempty t nonempty-t)) wt in
         let s2 = ht-to-string h in
         let mp = build-mapping h in
         let s3 = trie-to-string " <- " (λ s → s) mp in
         let s4 = "! " ^ s3 ^ (encode-words mp ww) in
           encode-output s1 s2 s3 s4
process-cmd (Decode cs v) =
  let ct = make-code-tree ct-empty cs in
  let s = decode-string ct v in
    decode-output s

process-start : start → output-type
process-start (File c) = process-cmd c 

process : Run → output-type
process (ParseTree (parsed-start p) :: []) = process-start p
process r = error-output ("Parsing failure (run with -" ^ "-showParsed).\n")

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

doOutput : output-type → string → IO ⊤
doOutput (error-output s) basename = putStr ("Error: " ^ s ^ "\n")
doOutput (encode-output s1 s2 s3 s4) basename = 
  writeFile (basename ^ "-frequencies.txt") s1 >> 
  writeFile (basename ^ ".gv") s2 >>
  writeFile (basename ^ "-mapping.txt") s3 >>
  writeFile (basename ^ ".huff") s4
doOutput (decode-output s) basename = writeFile (basename ^ "-decoded.txt") s

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed (input-filename :: []) = (readFiniteFile input-filename) >>= processText
  where processText : string → IO ⊤
        processText x with runRtn (string-to-𝕃char x)
        processText x | s with s
        processText x | s | inj₁ cs = putStr "Characters left before failure : " >> putStr (𝕃char-to-string cs) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> doOutput (process r') (base-filename input-filename)
                                     
processArgs showRun showParsed ("--showRun" :: xs) = processArgs tt showParsed xs 
processArgs showRun showParsed ("--showParsed" :: xs) = processArgs showRun tt xs 
processArgs showRun showParsed (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff

