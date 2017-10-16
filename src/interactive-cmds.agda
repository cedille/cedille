module interactive-cmds where

import parse
import run
open import lib
open import cedille-types

-- for parser for Cedille source files
open import cedille
module parsem = parse gratr2-nt ptr
open parsem.pnoderiv rrs cedille-rtn

module pr = run ptr
open pr.noderiv {- from run.agda -}

open import conversion
open import ctxt
open import general-util
open import spans
open import syntax-util
open import to-string
open import toplevel-state
open import untyped-spans

{- Getters/Converters -}

string-to-𝔹 : string → 𝔹
string-to-𝔹 "tt" = tt
string-to-𝔹 _ = ff

{- General -}

-- sep : string
sep = "§"

parse-specific-nt : gratr2-nt → ℕ → (lc : 𝕃 char) → 𝕃 char ⊎ Run
parse-specific-nt nt starting-char-position lc with parse-filter lc lc [] [] (cedille-start nt) inj₁
...| inj₁ left = inj₁ left
...| inj₂ run = inj₂ (re-to-run starting-char-position (reverse run))


{- Context code -}

local-ctxt-item : Set
local-ctxt-item = string × string × string × string × string × string -- language-level , name , value , type , filename , position

get-term-from-run : Run → (do-erase : 𝔹) → term
get-term-from-run ((ParseTree (parsed-term t)) :: []) de = if de then erase-term t else t
get-term-from-run _ _ = Var "" "error-at-get-term-from-run"
get-type-from-run : Run → type
get-type-from-run ((ParseTree (parsed-type t)) :: []) = t
get-type-from-run _ = TpVar "" "error-at-get-type-from-run"
get-kind-from-run : Run → kind
get-kind-from-run ((ParseTree (parsed-kind k)) :: []) = k
get-kind-from-run _ = KndVar "" "error-at-get-kind-from-run" (ArgsNil "")

return-tree : gratr2-nt → (maybe Run) → Run → var → string → string → (do-erase : 𝔹) → ctxt → ctxt
return-tree gratr2-nt._term (just val-run) tp-run v fn pos de Γ = ctxt-term-def pos localScope v (get-term-from-run val-run de) (get-type-from-run tp-run) (ctxt-set-current-file Γ fn)
return-tree gratr2-nt._type (just val-run) tp-run v fn pos de Γ = ctxt-type-def pos localScope v (get-type-from-run val-run) (get-kind-from-run tp-run) (ctxt-set-current-file Γ fn)
return-tree gratr2-nt._term nothing tp-run v fn pos de Γ = ctxt-term-decl pos v (get-type-from-run tp-run) (ctxt-set-current-file Γ fn)
return-tree gratr2-nt._type nothing tp-run v fn pos de Γ = ctxt-type-decl pos v (get-kind-from-run tp-run) (ctxt-set-current-file Γ fn)
return-tree _ _ _ _ _ _ _ Γ = Γ

return-run : gratr2-nt → 𝕃 char ⊎ Run → 𝕃 char ⊎ Run → var → string → string → (do-erase : 𝔹) → ctxt → ctxt
return-run nt (inj₂ val-run) (inj₂ tp-run) v fn pos de Γ =
  (λ original-file → ctxt-set-current-file (return-tree nt (just (rewriteRun val-run)) (rewriteRun tp-run) v fn pos de Γ) original-file) (ctxt-get-current-filename Γ)
return-run nt (inj₁ _) (inj₂ tp-run) v fn pos de Γ =
  (λ original-file → ctxt-set-current-file (return-tree nt nothing (rewriteRun tp-run) v fn pos de Γ) original-file) (ctxt-get-current-filename Γ)
return-run _ _ _ _ _ _ _ Γ = Γ

merge-lci-ctxt-h-h : gratr2-nt → string → 𝕃 char ⊎ Run
merge-lci-ctxt-h-h nt "" = inj₁ []
merge-lci-ctxt-h-h nt s = parse-specific-nt nt 0 (string-to-𝕃char s)

merge-lci-ctxt-h : gratr2-nt → gratr2-nt → (name : string) → (value : string) → (t-k : string) → string → string → (do-erase : 𝔹) → ctxt → ctxt
merge-lci-ctxt-h val-nt tp-nt name val t-k fn pos de Γ with parse-specific-nt val-nt 0 (string-to-𝕃char val) | parse-specific-nt tp-nt 0 (string-to-𝕃char t-k)
merge-lci-ctxt-h nt _ name _ _ fn pos de Γ | val-run | tp-run = return-run nt val-run tp-run name fn pos de Γ
-- return-run nt (parse-specific-nt nt 0 (string-to-𝕃char t-k)) name fn pos Γ

merge-lci-ctxt : local-ctxt-item → (do-erase : 𝔹) → ctxt → ctxt
merge-lci-ctxt ("term" , name , value , tp , filename , pos) de Γ = merge-lci-ctxt-h gratr2-nt._term gratr2-nt._type name value tp filename pos de Γ
merge-lci-ctxt ("type" , name , value , tp , filename , pos) de Γ = merge-lci-ctxt-h gratr2-nt._type gratr2-nt._kind name value tp filename pos de Γ
merge-lci-ctxt _ _ Γ = Γ

merge-lcis-ctxt : 𝕃 local-ctxt-item → (do-erase : 𝔹) → ctxt → ctxt
merge-lcis-ctxt (h :: t) de Γ = merge-lcis-ctxt t de (merge-lci-ctxt h de Γ)
merge-lcis-ctxt [] _ Γ = Γ
    
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

get-local-ctxt : (pos : ℕ) → (filename : string) → (local-ctxt : 𝕃 string) → ctxt → (do-erase : 𝔹) → ctxt
get-local-ctxt pos filename local-ctxt Γ de = merge-lcis-ctxt (strings-to-lcis local-ctxt) de (ctxt-at pos filename Γ)
  where
    strings-to-lcis-h : 𝕃 string → 𝕃 local-ctxt-item → 𝕃 local-ctxt-item
    strings-to-lcis-h (ll :: name :: val :: tp :: filename :: pos :: t) items =
      strings-to-lcis-h t ((ll , name , val , tp , filename , pos) :: items)
    strings-to-lcis-h _ items = items
    
    strings-to-lcis : 𝕃 string → 𝕃 local-ctxt-item
    strings-to-lcis ss = strings-to-lcis-h ss []





{- Normalize code -}
-- {ed : exprd} → 
-- add-parentheses : ctxt → ⟦ ed ⟧ → 𝔹 → string
add-parentheses : {ed : exprd} → ctxt → 𝔹 → ⟦ ed ⟧ → string
add-parentheses{TERM} Γ ap = term-to-string Γ (~ ap)
add-parentheses{TYPE} Γ ap = type-to-string Γ (~ ap)
add-parentheses{KIND} Γ ap = kind-to-string Γ (~ ap)
add-parentheses{LIFTINGTYPE} Γ ap = liftingType-to-string Γ

normalize-tree : ctxt → (input : string) → Run → 𝔹 → 𝔹 → string × 𝔹
normalize-tree Γ input (ParseTree (parsed-term t) :: []) head ap = (add-parentheses Γ ap (hnf Γ (unfold (~ head) ff ff) t tt)) , tt
normalize-tree Γ input (ParseTree (parsed-type t) :: []) head ap = (add-parentheses Γ ap (hnf Γ (unfold (~ head) ff ff) t tt)) , tt
normalize-tree _ input  _ _ _ = input , ff

normalize-Run-or-error : ctxt → (input : string) → 𝕃 char ⊎ Run → (head : 𝔹) → (add-parens : 𝔹) → string × 𝔹
normalize-Run-or-error _ input (inj₁ chars) head _ = input , ff
normalize-Run-or-error Γ input (inj₂ run) head ap = normalize-tree Γ input (rewriteRun run) head ap

normalize-span : ctxt → gratr2-nt → string → (pos : ℕ) → (head : 𝔹) → (add-parens : 𝔹) → string × 𝔹 
normalize-span Γ nt text sp head ap = normalize-Run-or-error Γ text (parse-specific-nt nt sp (string-to-𝕃char text)) head ap

normalize-cmd : (start-pos : ℕ) → (span-str : string) → ctxt → (lang-level : string) → (filename : string) → (head : 𝔹) → (add-parens : 𝔹) → (do-erase : 𝔹) → (local-ctxt : 𝕃 string) → string × 𝔹
normalize-cmd _ _ _ ll _ _ _ _ _ with get-nt ll
  where
    get-nt : string → maybe gratr2-nt
    get-nt "term" = just gratr2-nt._term
    get-nt "type" = just gratr2-nt._type
    get-nt _ = nothing
normalize-cmd _ ss _ _ _ _ _ _ _ | nothing = ss , ff
normalize-cmd sp ss Γ _ fn head ap de lc | (just nt) = normalize-span (get-local-ctxt sp fn lc Γ de) nt ss sp head ap

normalize-just-run : maybe Run → ctxt → (input : string) → (head : 𝔹) → (add-parens : 𝔹) → string × 𝔹
normalize-just-run (just run) Γ input head ap = normalize-tree Γ input (rewriteRun run) head ap
normalize-just-run nothing _ input _ _ = input , ff

normalize-prompt : (input : string) → ctxt → (head : 𝔹) → string × 𝔹
normalize-prompt input _ _ with string-to-𝕃char input
normalize-prompt input _ _ | chars with parse-specific-nt gratr2-nt._term 0 chars
normalize-prompt input _ _ | chars | _ with parse-specific-nt gratr2-nt._type 0 chars
normalize-prompt _ _ _ | _ | term-run | type-run with choose-run term-run type-run
  where
    choose-run : (term-run : 𝕃 char ⊎ Run) → (type-run : 𝕃 char ⊎ Run) → maybe Run
    choose-run (inj₂ run) _ = just run
    choose-run _ (inj₂ run) = just run
    choose-run _ _ = nothing
normalize-prompt input Γ head | _ | _ | _ | just-run with normalize-just-run just-run Γ input head ff
normalize-prompt input _ head | _ | _ | _ | _ | (str , tt) = ("Expression: " ^ input ^ norm-str ^ str) , tt
  where norm-str = if head then "\nHead-normalized: " else "\nNormalized: "
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


{- Beta reduction code -}

br-parse-try : 𝕃 char → 𝕃 gratr2-nt → maybe Run
br-parse-try _ [] = nothing
br-parse-try lc (h :: t) with parse-specific-nt h 0 lc
br-parse-try lc (h :: t) | inj₁ _ = br-parse-try lc t
br-parse-try lc (h :: t) | inj₂ run = just (rewriteRun run)

try-nts : 𝕃 gratr2-nt
try-nts = (gratr2-nt._term :: gratr2-nt._type :: gratr2-nt._kind :: gratr2-nt._cmd :: [])

br-put-spans : spanM ⊤ → IO ⊤
br-put-spans sM = putStrLn (spans-to-string (snd (snd (sM (new-ctxt "") (regular-spans [])))))

br-parse : 𝕃 char → ctxt → IO ⊤
br-parse lc _ with br-parse-try lc try-nts
br-parse lc Γ | just (ParseTree (parsed-term t) :: []) = br-put-spans
  (set-ctxt Γ ≫span erased-spans t)
br-parse lc Γ | _ = putStrLn (global-error-string "Error parsing \"" ^ (𝕃char-to-string lc) ^ "\"")

{-
br-parse : 𝕃 char → ctxt → IO ⊤
br-parse lc _ with br-parse-try lc try-nts
br-parse lc Γ | just (ParseTree (parsed-term t) :: []) = br-put-spans
  (set-ctxt Γ ≫span untyped-term t)
br-parse lc Γ | just (ParseTree (parsed-type tp) :: []) = br-put-spans
  (set-ctxt Γ ≫span untyped-type tp)
br-parse lc Γ | just (ParseTree (parsed-kind k) :: []) = br-put-spans
  (set-ctxt Γ ≫span untyped-kind k)
br-parse lc Γ | just (ParseTree (parsed-cmd c) :: []) = br-put-spans
  (set-ctxt Γ ≫span untyped-cmd c)
br-parse lc _ | just (ParseTree pt :: []) = putStrLn (global-error-string "Strange ParseTree item in br-parse")
br-parse lc _ | nothing = putStrLn (global-error-string ("Error parsing \"" ^ (𝕃char-to-string lc) ^ "\""))
br-parse lc _ | _ = putStrLn (global-error-string "This shouldn't happen in br-parse")
-}

{- Conversion -}

conv-runs : ctxt → Run → Run → string × 𝔹
conv-runs Γ (ParseTree (parsed-term t₁) :: []) (ParseTree (parsed-term t₂) :: []) = (𝔹-to-string (conv-term Γ t₁ t₂)) , tt
conv-runs _ (ParseTree (parsed-term t₁) :: []) r₂ = Run-to-string r₂ , ff
conv-runs _ r₁ (ParseTree (parsed-term t₂) :: []) = Run-to-string r₁ , ff
conv-runs _ r₁ r₂ = (Run-to-string r₁) ^ "\" and \"" ^ (Run-to-string r₂) , ff

conv : ctxt → string → string → string × 𝔹
conv _ s₁ s₂ with parse-specific-nt gratr2-nt._term 0 (string-to-𝕃char s₁) | parse-specific-nt gratr2-nt._term 0 (string-to-𝕃char s₂)
conv _ s₁ s₂ | (inj₁ lc) | _ = s₁ , ff
conv _ s₁ s₂ | (inj₂ run₁) | (inj₁ lc) = s₂ , ff
conv Γ s₁ s₂ | (inj₂ run₁) | (inj₂ run₂) = conv-runs Γ (rewriteRun run₁) (rewriteRun run₂)



{- Commands -}

interactive-return : string × 𝔹 → toplevel-state → IO toplevel-state
interactive-return (str , tt) ts = putStrLn (escape-string str) >> return ts
interactive-return (str , ff) ts = putStrLn (global-error-string ("Error parsing \"" ^ (escape-string str) ^ "\"")) >> return ts

add-ws : 𝕃 char → 𝕃 char
add-ws (' ' :: lc) = ' ' :: lc
add-ws lc = ' ' :: lc

-- Makes the string more aesthetically pleasing by removing newlines,
-- replacing tabs with spaces, and removing unnecessary double whitespaces.
-- Also, interactive parsing fails if there are newlines anywhere or periods at the end.
pretty-string-h : 𝔹 → 𝕃 char → 𝕃 char → 𝕃 char
pretty-string-h p ('\n' :: rest) so-far = pretty-string-h p rest (add-ws so-far)
pretty-string-h p (' ' :: rest) so-far = pretty-string-h p rest (add-ws so-far)
pretty-string-h p ('\t' :: rest) so-far = pretty-string-h p rest (add-ws so-far)
pretty-string-h p (c :: rest) so-far = pretty-string-h p rest (c :: so-far)
pretty-string-h p [] so-far = reverse (remove-proceeding-ws-period so-far p)
  where
    remove-proceeding-ws-period : 𝕃 char → 𝔹 → 𝕃 char
    remove-proceeding-ws-period (' ' :: rest) p = remove-proceeding-ws-period rest p
    remove-proceeding-ws-period ('.' :: rest) tt = remove-proceeding-ws-period rest p
    remove-proceeding-ws-period rest _ = rest

pretty-string : string → (remove-period : 𝔹) → string
pretty-string str p = 𝕃char-to-string (pretty-string-h p (string-to-𝕃char str) [])

interactive-normalize-span : 𝕃 string → toplevel-state → IO toplevel-state
interactive-normalize-span (start-str :: span-str :: lang-level :: filename :: head-str :: add-parens :: do-erase :: local-ctxt) ts =
  interactive-return (normalize-cmd (posinfo-to-ℕ start-str) (pretty-string span-str tt) (toplevel-state.Γ ts) lang-level filename (string-to-𝔹 head-str) (string-to-𝔹 add-parens) (string-to-𝔹 do-erase) local-ctxt) ts
interactive-normalize-span _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-normalize-span") >> return ts

interactive-erase-span : 𝕃 string → toplevel-state →  IO toplevel-state
interactive-erase-span (start-str :: span-str :: filename :: local-ctxt) ts =
  interactive-return (erase-span (get-local-ctxt sp filename local-ctxt (toplevel-state.Γ ts) tt) (pretty-string span-str tt) sp) ts
  where sp = (posinfo-to-ℕ start-str)
interactive-erase-span _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-erase-span") >> return ts

interactive-normalize-prompt : 𝕃 string → toplevel-state → IO toplevel-state
interactive-normalize-prompt (span-str :: head-str :: filename :: local-ctxt) ts =
  interactive-return (normalize-prompt (pretty-string span-str tt) (get-local-ctxt 0 filename local-ctxt (toplevel-state.Γ ts) ff) (string-to-𝔹 head-str)) ts
interactive-normalize-prompt _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-normalize-prompt") >> return ts

interactive-erase-prompt : 𝕃 string → toplevel-state → IO toplevel-state
interactive-erase-prompt (span-str :: filename :: local-ctxt) ts =
  interactive-return (erase-prompt (pretty-string span-str tt) (get-local-ctxt 0 filename local-ctxt (toplevel-state.Γ ts) tt)) ts
interactive-erase-prompt _ ts =
  putStrLn (global-error-string "Wrong number of arguments given to interactive-erase-prompt") >> return ts

interactive-br-parse : 𝕃 string → toplevel-state → IO toplevel-state
interactive-br-parse (fn :: str :: []) ts = br-parse (string-to-𝕃char (pretty-string str ff)) (ctxt-set-current-file (toplevel-state.Γ ts) fn) >> return ts
-- interactive-br-parse (str :: []) ts = putStrLn (br-parse str) >>= λ _ → return ts
interactive-br-parse _ ts = putStrLn (global-error-string "Wrong number of argument given to interactive-br-parse") >> return ts

interactive-conv : 𝕃 string → toplevel-state → IO toplevel-state
interactive-conv (t₁ :: t₂ :: []) ts = interactive-return (conv (toplevel-state.Γ ts) t₁ t₂) ts
interactive-conv _ ts = putStrLn (global-error-string "Wrong number of arguments given to interactive-conv") >> return ts
