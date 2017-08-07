module interactive-cmds where

open import cedille
open import conversion
open import ctxt
open import general-util
open import spans
open import syntax-util
open import to-string
open import toplevel-state

import parse
open import lib
open import cedille-types

module parsem = parse gratr2-nt ptr
open parsem
open parsem.pnoderiv rrs cedille-rtn
open import run ptr
open noderiv {- from run.agda -}



{- Getters/Converters -}

ts-to-ctxt : toplevel-state → ctxt
ts-to-ctxt (mk-toplevel-state _ _ _ _ Γ) = Γ

string-to-𝔹 : string → 𝔹
string-to-𝔹 "tt" = tt
string-to-𝔹 _ = ff

{- General -}

parse-specific-nt : gratr2-nt → ℕ → (lc : 𝕃 char) → 𝕃 char ⊎ Run
parse-specific-nt nt starting-char-position lc with parse-filter lc lc [] [] (cedille-start nt) inj₁
...| inj₁ left = inj₁ left
...| inj₂ run = inj₂ (re-to-run starting-char-position (reverse run))


{- Context code -}

local-ctxt-item : Set
local-ctxt-item = string × string × string × string × string -- language-level , name , value , filename , position

get-type-from-run : Run → type
get-type-from-run ((ParseTree (parsed-type t)) :: []) = t
get-type-from-run _ = TpVar "" "error-at-get-type-from-run"
get-kind-from-run : Run → kind
get-kind-from-run ((ParseTree (parsed-kind k)) :: []) = k
get-kind-from-run _ = KndVar "" "error-at-get-kind-from-run" (ArgsNil "")

return-tree : gratr2-nt → Run → var → string → string → ctxt → ctxt
return-tree gratr2-nt._type run v fn pos Γ = ctxt-term-decl pos v (get-type-from-run run) (ctxt-set-current-file Γ fn)
return-tree gratr2-nt._kind run v fn pos Γ = ctxt-type-decl pos v (get-kind-from-run run) (ctxt-set-current-file Γ fn)
return-tree _ _ _ _ _ Γ = Γ

return-run : gratr2-nt → 𝕃 char ⊎ Run → var → string → string → ctxt → ctxt
return-run nt (inj₂ run) v fn pos Γ = (λ original-file → ctxt-set-current-file (return-tree nt (rewriteRun run) v fn pos Γ) original-file) (ctxt-get-current-filename Γ)
return-run _ _ _ _ _ Γ = Γ

merge-lci-ctxt-h : gratr2-nt → (name : string) → (t-k : string) → string → string → ctxt → ctxt
merge-lci-ctxt-h nt name t-k fn pos Γ =
  return-run nt (parse-specific-nt nt 0 (string-to-𝕃char t-k)) name fn pos Γ

merge-lci-ctxt : local-ctxt-item → ctxt → ctxt
merge-lci-ctxt ("term" , name , value , filename , pos) = merge-lci-ctxt-h gratr2-nt._type name value filename pos
merge-lci-ctxt ("type" , name , value , filename , pos) = merge-lci-ctxt-h gratr2-nt._kind name value filename pos
merge-lci-ctxt _ Γ = Γ

merge-lcis-ctxt : 𝕃 local-ctxt-item → ctxt → ctxt
merge-lcis-ctxt (h :: t) Γ = merge-lcis-ctxt t (merge-lci-ctxt h Γ)
merge-lcis-ctxt [] Γ = Γ
    
to-nyd-h : trie sym-info → string → ℕ → (so-far : 𝕃 (sym-info × string)) → (path : 𝕃 char) → 𝕃 (sym-info × string)
to-nyd-h (Node msi ((c , h) :: t)) fn pos sf path = to-nyd-h (Node msi t) fn pos (to-nyd-h h fn pos sf (c :: path)) path
to-nyd-h (Node (just (ci , fp , pi)) []) fn pos sf path = if nyd then (((ci , fp , pi) , (𝕃char-to-string (reverse path))) :: sf) else sf
  where nyd = (fp =string fn) && ((posinfo-to-ℕ pi) > pos)
to-nyd-h _ _ _ sf _ = sf

to-nyd : trie sym-info → (filename : string) → (pos : ℕ) → 𝕃 (sym-info × string)
to-nyd tr fn pos = to-nyd-h tr fn pos [] []

ctxt-at : (pos : ℕ) → (filename : string) → ctxt → ctxt
ctxt-at pos filename Γ = ctxt-nyd-all (ctxt-set-current-file Γ filename) (to-nyd (get-si Γ) filename pos)
  where
    ctxt-nyd-all : ctxt → 𝕃 (sym-info × string) → ctxt
    ctxt-nyd-all Γ ((_ , v) :: t) = ctxt-nyd-all (ctxt-clear-symbol Γ v) t
    ctxt-nyd-all Γ [] = Γ

    get-si : ctxt → trie sym-info
    get-si (mk-ctxt _ _ si _) = si

get-local-ctxt : (pos : ℕ) → (filename : string) → (local-ctxt : 𝕃 string) → ctxt → ctxt
get-local-ctxt pos filename local-ctxt Γ = merge-lcis-ctxt (strings-to-lcis local-ctxt) (ctxt-at pos filename Γ)
  where
    strings-to-lcis-h : 𝕃 string → 𝕃 local-ctxt-item → 𝕃 local-ctxt-item
    strings-to-lcis-h (ll :: name :: val :: filename :: pos :: t) items =
      strings-to-lcis-h t ((ll , name , val , filename , pos) :: items)
    strings-to-lcis-h _ items = items
    
    strings-to-lcis : 𝕃 string → 𝕃 local-ctxt-item
    strings-to-lcis ss = strings-to-lcis-h ss []





{- Normalize code -}

normalize-tree : ctxt → (input : string) → Run → 𝔹 → string × 𝔹
normalize-tree Γ input (ParseTree (parsed-term t) :: []) full = (to-string Γ (hnf Γ (unfold full ff ff) t tt)) , tt
normalize-tree Γ input (ParseTree (parsed-type t) :: []) full = (to-string Γ (hnf Γ (unfold full ff ff) t tt)) , tt
normalize-tree _ input  _ _ = input , ff

normalize-Run-or-error : ctxt → (input : string) → 𝕃 char ⊎ Run → 𝔹 → string × 𝔹
normalize-Run-or-error _ input (inj₁ chars) full = input , ff
normalize-Run-or-error Γ input (inj₂ run) full = normalize-tree Γ input (rewriteRun run) full

normalize-span : ctxt → gratr2-nt → string → ℕ → 𝔹 → string × 𝔹 
normalize-span Γ nt text sp full = normalize-Run-or-error Γ text (parse-specific-nt nt sp (string-to-𝕃char text)) full

normalize-cmd : (start-pos : ℕ) → (span-str : string) → ctxt → (lang-level : string) → (filename : string) → (full : 𝔹) → (local-ctxt : 𝕃 string) → string × 𝔹
normalize-cmd _ _ _ ll _ _ _ with get-nt ll
  where
    get-nt : string → maybe gratr2-nt
    get-nt "term" = just gratr2-nt._term
    get-nt "type" = just gratr2-nt._type
    get-nt _ = nothing
normalize-cmd _ ss _ _ _ _ _ | nothing = ss , ff
normalize-cmd sp ss Γ _ fn full lc | (just nt) = normalize-span (get-local-ctxt sp fn lc Γ) nt ss sp full

normalize-just-run : maybe Run → ctxt → (input : string) → (full : 𝔹) → string × 𝔹
normalize-just-run (just run) Γ input full = normalize-tree Γ input (rewriteRun run) full
normalize-just-run nothing _ input _ = input , ff

normalize-prompt : (input : string) → ctxt → (full : 𝔹) → string × 𝔹
normalize-prompt input _ _ with string-to-𝕃char input
normalize-prompt input _ _ | chars with parse-specific-nt gratr2-nt._term 0 chars
normalize-prompt input _ _ | chars | _ with parse-specific-nt gratr2-nt._type 0 chars
normalize-prompt _ _ _ | _ | term-run | type-run with choose-run term-run type-run
  where
    choose-run : (term-run : 𝕃 char ⊎ Run) → (type-run : 𝕃 char ⊎ Run) → maybe Run
    choose-run (inj₂ run) _ = just run
    choose-run _ (inj₂ run) = just run
    choose-run _ _ = nothing
normalize-prompt input Γ full | _ | _ | _ | just-run with normalize-just-run just-run Γ input full
normalize-prompt input _ full | _ | _ | _ | _ | (str , tt) = ("Expression: " ^ input ^ norm-str ^ str) , tt
  where norm-str = if full then "\nNormalized: " else "\nHead-normalized: "
normalize-prompt _ _ _ | _ | _ | _ | _ | error = error



{- Erasure code -}

erase-tree : ctxt → (input : string) → Run → string × 𝔹
erase-tree Γ input (ParseTree (parsed-term t) :: []) = (to-string Γ (erase-term t)) , tt
erase-tree _ input _ = input , ff

erase-run : (input : string) → 𝕃 char ⊎ Run → ctxt → string × 𝔹
erase-run input (inj₁ _) Γ = input , ff
erase-run input (inj₂ run) Γ = erase-tree Γ input (rewriteRun run)

erase-span : ctxt → string → ℕ → string × 𝔹
erase-span Γ str start-pos = erase-run str (parse-specific-nt gratr2-nt._term start-pos (string-to-𝕃char str)) Γ

erase-inj-run : 𝕃 char ⊎ Run → (input : string) → ctxt → string × 𝔹
erase-inj-run (inj₂ run) input Γ = erase-tree Γ input (rewriteRun run)
erase-inj-run _ input _ = input , ff

erase-prompt-h : (input : string) → ctxt → 𝕃 char ⊎ Run → string × 𝔹
erase-prompt-h input Γ run with erase-inj-run run input Γ
erase-prompt-h input _ _ | (str , tt) = ("Expression: " ^ input ^ "\nErased: " ^ str) , tt
erase-prompt-h _ _ _ | error = error

erase-prompt : (input : string) → ctxt → string × 𝔹
erase-prompt input Γ =
  erase-prompt-h input Γ (parse-specific-nt gratr2-nt._term 0 (string-to-𝕃char input))


{- Commands -}

interactive-return : string × 𝔹 → toplevel-state → IO toplevel-state
interactive-return (str , tt) ts = putStrLn (escape-string str) >>= λ _ → return ts
interactive-return (str , ff) ts = putStrLn (global-error-string ("Error parsing \"" ^ (escape-string str) ^ "\"")) >>= λ _ → return ts

add-ws : 𝕃 char → 𝕃 char
add-ws (' ' :: lc) = ' ' :: lc
add-ws lc = ' ' :: lc

-- Makes the string more aesthetically pleasing by removing newlines,
-- replacing tabs with spaces, and removing unnecessary double whitespaces.
-- Also, interactive parsing fails if there are newlines anywhere or periods at the end.
pretty-string-h : 𝕃 char → 𝕃 char → 𝕃 char
pretty-string-h ('\n' :: rest) so-far = pretty-string-h rest (add-ws so-far)
pretty-string-h (' ' :: rest) so-far = pretty-string-h rest (add-ws so-far)
pretty-string-h ('\t' :: rest) so-far = pretty-string-h rest (add-ws so-far)
pretty-string-h (c :: rest) so-far = pretty-string-h rest (c :: so-far)
pretty-string-h [] so-far = reverse (remove-proceeding-ws-period so-far)
  where
    remove-proceeding-ws-period : 𝕃 char → 𝕃 char
    remove-proceeding-ws-period (' ' :: rest) = remove-proceeding-ws-period rest
    remove-proceeding-ws-period ('.' :: rest) = remove-proceeding-ws-period rest
    remove-proceeding-ws-period rest = rest

pretty-string : string → string
pretty-string str = 𝕃char-to-string (pretty-string-h (string-to-𝕃char str) [])

interactive-normalize-span : 𝕃 string → toplevel-state → IO toplevel-state
interactive-normalize-span (start-str :: span-str :: lang-level :: filename :: full-str :: local-ctxt) ts =
  interactive-return (normalize-cmd (posinfo-to-ℕ start-str) (pretty-string span-str) (ts-to-ctxt ts) lang-level filename (string-to-𝔹 full-str) local-ctxt) ts
interactive-normalize-span _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-normalize-span") >>= λ _ → return ts

interactive-erase-span : 𝕃 string → toplevel-state →  IO toplevel-state
interactive-erase-span (start-str :: span-str :: filename :: local-ctxt) ts =
  interactive-return (erase-span (get-local-ctxt sp filename local-ctxt (ts-to-ctxt ts)) (pretty-string span-str) sp) ts
  where sp = (posinfo-to-ℕ start-str)
interactive-erase-span _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-erase-span") >>= λ _ → return ts

interactive-normalize-prompt : 𝕃 string → toplevel-state → IO toplevel-state
interactive-normalize-prompt (span-str :: full-str :: rest) ts =
  interactive-return (normalize-prompt (pretty-string span-str) (ts-to-ctxt ts) (string-to-𝔹 full-str)) ts
interactive-normalize-prompt _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-normalize-prompt") >>= λ _ → return ts

interactive-erase-prompt : 𝕃 string → toplevel-state → IO toplevel-state
interactive-erase-prompt (span-str :: []) ts =
  interactive-return (erase-prompt (pretty-string span-str) (ts-to-ctxt ts)) ts
interactive-erase-prompt _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-erase-prompt") >>= λ _ → return ts
