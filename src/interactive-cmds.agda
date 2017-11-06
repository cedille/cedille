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

{- General -}

parse-specific-nt : gratr2-nt → ℕ → (lc : 𝕃 char) → 𝕃 char ⊎ Run
parse-specific-nt nt starting-char-position lc with parse-filter lc lc [] [] (cedille-start nt) inj₁
...| inj₁ left = inj₁ left
...| inj₂ run = inj₂ (re-to-run starting-char-position (reverse run))

parse-try-nts : 𝕃 char → 𝕃 gratr2-nt → maybe Run
parse-try-nts _ [] = nothing
parse-try-nts lc (h :: t) with parse-specific-nt h 0 lc
parse-try-nts lc (h :: t) | inj₁ _ = parse-try-nts lc t
parse-try-nts lc (h :: t) | inj₂ run = just (rewriteRun run)

try-nts : 𝕃 gratr2-nt
try-nts = (gratr2-nt._term :: gratr2-nt._type :: gratr2-nt._kind :: [])

parse-ll-run : ctxt → Run → Run
parse-ll-run Γ (ParseTree (parsed-term (Var pi v)) :: []) with ctxt-lookup-term-var-def Γ v | ctxt-lookup-type-var-def Γ v
parse-ll-run Γ (ParseTree (parsed-term (Var pi v)) :: []) | nothing | just tp = ParseTree (parsed-type (TpVar pi v)) :: []
parse-ll-run Γ run @ (ParseTree (parsed-term (Var pi v)) :: []) | _ | _ = run
parse-ll-run Γ run = run

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

parse-error-message : (failed-to-parse : string) → (as-a : string) → string × 𝔹
parse-error-message failed-to-parse as-a = "Failed to parse \"" ^ failed-to-parse ^ "\" as a " ^ as-a , ff

string-to-𝔹 : string → maybe 𝔹
string-to-𝔹 "tt" = just tt
string-to-𝔹 "ff" = just ff
string-to-𝔹 _ = nothing

nt-to-string : gratr2-nt → string
nt-to-string gratr2-nt._term = "term"
nt-to-string gratr2-nt._type = "type"
nt-to-string gratr2-nt._kind = "kind"
nt-to-string _ = "[error: invalid nonterminal (src/interactive-cmds.agda/nt-to-string)]"


{- Context code -}

local-ctxt-item : Set
local-ctxt-item = string × string × string × string × string × string -- language-level , name , value , type , filename , position

get-term-from-run : Run → maybe cedille-types.term
get-type-from-run : Run → maybe cedille-types.type
get-kind-from-run : Run → maybe cedille-types.kind
get-term-from-run ((ParseTree (parsed-term t)) :: []) = just t
get-term-from-run _ = nothing
get-type-from-run ((ParseTree (parsed-type tp)) :: []) = just tp
get-type-from-run _ = nothing
get-kind-from-run ((ParseTree (parsed-kind k)) :: []) = just k
get-kind-from-run _ = nothing

ctxt-def-tree : ctxt → gratr2-nt → (maybe Run) → Run → var → string → string → (do-erase : 𝔹) → ctxt
ctxt-def-tree Γ gratr2-nt._term (just val-run) tp-run v fn pos de with get-term-from-run val-run | get-type-from-run tp-run
ctxt-def-tree Γ gratr2-nt._term (just _) _ v fn pos de | just t | just tp = ctxt-term-def pos localScope v (if de then (erase-term t) else t) tp Γ
ctxt-def-tree Γ gratr2-nt._term (just val-run) _ _ _ _ _ | _ | _ = Γ
ctxt-def-tree Γ gratr2-nt._type (just val-run) tp-run _ _ _ _ with get-type-from-run val-run | get-kind-from-run tp-run
ctxt-def-tree Γ gratr2-nt._type (just val-run) tp-run v fn pos _ | just tp | just k = ctxt-type-def pos localScope v tp k Γ
ctxt-def-tree Γ gratr2-nt._type (just val-run) _ _ _ _ _ | _ | _ = Γ
ctxt-def-tree Γ gratr2-nt._term nothing tp-run v fn pos _ with get-type-from-run tp-run
ctxt-def-tree Γ gratr2-nt._term nothing _ v fn pos de | just tp = ctxt-term-decl pos v tp Γ
ctxt-def-tree Γ gratr2-nt._term nothing _ _ _ _ _ | nothing = Γ
ctxt-def-tree Γ gratr2-nt._type nothing tp-run v fn pos _ with get-kind-from-run tp-run
ctxt-def-tree Γ gratr2-nt._type nothing _ v fn pos _ | just k = ctxt-type-decl pos v k Γ
ctxt-def-tree Γ gratr2-nt._type nothing _ _ _ _ _ | nothing = Γ
ctxt-def-tree Γ _ _ _ _ _ _ _ = Γ

ctxt-def-run : gratr2-nt → 𝕃 char ⊎ Run → 𝕃 char ⊎ Run → var → string → string → (do-erase : 𝔹) → ctxt → ctxt
ctxt-def-run nt (inj₂ val-run) (inj₂ tp-run) v fn pos de Γ =
  (λ original-file →
    ctxt-set-current-file (ctxt-def-tree (ctxt-set-current-file Γ fn) nt (just (rewriteRun val-run)) (rewriteRun tp-run) v fn pos de) original-file)
  (ctxt-get-current-filename Γ)
ctxt-def-run nt (inj₁ _) (inj₂ tp-run) v fn pos de Γ =
  (λ original-file →
    ctxt-set-current-file (ctxt-def-tree (ctxt-set-current-file Γ fn) nt nothing (rewriteRun tp-run) v fn pos de) original-file)
  (ctxt-get-current-filename Γ)
ctxt-def-run _ _ _ _ _ _ _ Γ = Γ

merge-lci-ctxt-h-h : gratr2-nt → string → 𝕃 char ⊎ Run
merge-lci-ctxt-h-h nt "" = inj₁ []
merge-lci-ctxt-h-h nt s = parse-specific-nt nt 0 (string-to-𝕃char s)

merge-lci-ctxt-h : gratr2-nt → gratr2-nt → (name : string) → (value : string) → (t-k : string) → string → string → (do-erase : 𝔹) → ctxt → ctxt
merge-lci-ctxt-h val-nt tp-nt name val t-k fn pos de Γ with parse-specific-nt val-nt 0 (string-to-𝕃char val) | parse-specific-nt tp-nt 0 (string-to-𝕃char t-k)
merge-lci-ctxt-h nt _ name _ _ fn pos de Γ | val-run | tp-run = ctxt-def-run nt val-run tp-run name fn pos de Γ

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

strings-to-lcis : 𝕃 string → 𝕃 local-ctxt-item
strings-to-lcis ss = strings-to-lcis-h ss []
  where
    strings-to-lcis-h : 𝕃 string → 𝕃 local-ctxt-item → 𝕃 local-ctxt-item
    strings-to-lcis-h (ll :: name :: val :: tp :: filename :: pos :: t) items =
      strings-to-lcis-h t ((ll , name , val , tp , filename , pos) :: items)
    strings-to-lcis-h _ items = items

get-local-ctxt : ctxt → (pos : ℕ) → (filename : string) → (local-ctxt : 𝕃 string) → (do-erase : 𝔹) → ctxt
get-local-ctxt Γ pos filename local-ctxt de = merge-lcis-ctxt (strings-to-lcis local-ctxt) de (ctxt-at pos filename Γ)





{- Normalize code -}
add-parentheses : {ed : exprd} → ctxt → 𝔹 → ⟦ ed ⟧ → string
add-parentheses{TERM} Γ ap = term-to-string Γ (~ ap)
add-parentheses{TYPE} Γ ap = type-to-string Γ (~ ap)
add-parentheses{KIND} Γ ap = kind-to-string Γ (~ ap)
add-parentheses{LIFTINGTYPE} Γ ap = liftingType-to-string Γ
add-parentheses{ARG} Γ ap = arg-to-string Γ
add-parentheses{QUALIF} Γ ap = qualif-to-string Γ

normalize-tree : ctxt → (input : string) → Run → 𝔹 → string × 𝔹
normalize-tree Γ input (ParseTree (parsed-term t) :: []) head = (to-string Γ (hnf Γ (unfold (~ head) ff ff) t tt)) , tt
normalize-tree Γ input (ParseTree (parsed-type t) :: []) head = (to-string Γ (hnf Γ (unfold (~ head) ff ff) t tt)) , tt
normalize-tree _ input _ _ = "\"" ^ input ^ "\" was not parsed as a term or a type"  , ff

normalize-span : ctxt → (input : string) → gratr2-nt → (start-pos : ℕ) → (head : 𝔹) → string × 𝔹 
normalize-span _ input nt sp head with parse-specific-nt nt sp (string-to-𝕃char input)
normalize-span Γ input _ sp head | inj₂ run = normalize-tree Γ input (rewriteRun run) head
normalize-span _ input nt _ _ | inj₁ _ = parse-error-message input (nt-to-string nt)

normalize-cmd : ctxt → (span : string) → (lang-level : string) → (start-pos : string) → (filename : string) →
  (head : string) → (do-erase : string) → 𝕃 string → string × 𝔹
normalize-cmd _ _ ll sp fn head de _ with get-nt ll | string-to-ℕ sp | string-to-𝔹 head | string-to-𝔹 de
  where
    get-nt : string → maybe gratr2-nt
    get-nt "term" = just gratr2-nt._term
    get-nt "type" = just gratr2-nt._type
    get-nt _ = nothing
normalize-cmd Γ span _ _ fn _ _ local-ctxt | just ll | just sp | just head | just de =
  normalize-span (get-local-ctxt Γ sp fn local-ctxt de) (pretty-string span) ll sp head
normalize-cmd _ _ ll _ _ _ _ _ | nothing | _ | _ | _ = parse-error-message ll "language-level"
normalize-cmd _ _ _ sp _ _ _ _ | _ | nothing | _ | _ = parse-error-message sp "nat"
normalize-cmd _ _ _ _ _ hd _ _ | _ | _ | nothing | _ = parse-error-message hd "boolean"
normalize-cmd _ _ _ _ _ _ de _ | _ | _ | _ | nothing = parse-error-message de "boolean"

normalize-prompt : ctxt → (input : string) → (head : 𝔹) → string × 𝔹
normalize-prompt Γ input head with parse-try-nts (string-to-𝕃char input) (gratr2-nt._term :: gratr2-nt._type :: [])
normalize-prompt Γ input head | just run with normalize-tree Γ input (parse-ll-run Γ (rewriteRun run)) head
normalize-prompt Γ input head | just run | s , tt = "Expression: " ^ input ^ (if head then "\nHead-normalized: " else "\nNormalized: ") ^ s , tt
normalize-prompt Γ input _ | just run | error = error
normalize-prompt _ input _ | nothing = parse-error-message input "term or a type"

normalize-prompt-cmd : ctxt → (input : string) → (filename : string) → (head : string) → string × 𝔹
normalize-prompt-cmd Γ input fn head with string-to-𝔹 head
normalize-prompt-cmd Γ input fn _ | just head = normalize-prompt (ctxt-set-current-file Γ fn) (pretty-string input) head
normalize-prompt-cmd _ _ _ head | nothing = parse-error-message head "boolean"


{- Erasure code -}

erase-tree : ctxt → (input : string) → Run → string × 𝔹
erase-tree Γ input (ParseTree (parsed-term t) :: []) = to-string Γ (erase-term t) , tt
erase-tree _ input _ = parse-error-message input "term"

erase-span : ctxt → (input : string) → (start-pos : ℕ) → string × 𝔹
erase-span _ input sp with parse-specific-nt gratr2-nt._term sp (string-to-𝕃char input)
erase-span Γ input sp | inj₂ run = erase-tree Γ input (rewriteRun run)
erase-span _ input _ | inj₁ _ = parse-error-message input "term"

erase-cmd : ctxt → (input : string) → (start-pos : string) → (filename : string) → (local-ctxt : 𝕃 string) → string × 𝔹
erase-cmd Γ _ sp _ _ with string-to-ℕ sp
erase-cmd Γ input _ fn lc | just sp = erase-span (get-local-ctxt Γ sp fn lc ff) (pretty-string input) sp
erase-cmd _ _ sp _ _ | nothing = parse-error-message sp "nat"

erase-prompt-h : ctxt → (input : string) → 𝕃 char ⊎ Run → string × 𝔹
erase-prompt-h Γ input (inj₂ run) with erase-tree Γ input (parse-ll-run Γ (rewriteRun run))
erase-prompt-h _ input (inj₂ _) | s , tt = "Expression: " ^ input ^ "\nErased: " ^ s , tt
erase-prompt-h _ input (inj₂ _) | error = error
erase-prompt-h _ input (inj₁ _) = parse-error-message input "term"

erase-prompt : ctxt → (input : string) → (filename : string) → string × 𝔹
erase-prompt Γ input fn with pretty-string-h (string-to-𝕃char input) []
erase-prompt Γ _ fn | lc = erase-prompt-h (ctxt-set-current-file Γ fn) (𝕃char-to-string lc) (parse-specific-nt gratr2-nt._term 0 lc)


{- Beta reduction code -}

br-spans : spanM ⊤ → string × 𝔹
br-spans sM with snd (snd (sM (new-ctxt "") (regular-spans [])))
br-spans _ | global-error error ms = error , ff
br-spans _ | ss = spans-to-string ss , tt

br-parse : (input : string) → ctxt → string × 𝔹
br-parse input _ with parse-try-nts (string-to-𝕃char input) try-nts
br-parse _ Γ | just run with parse-ll-run Γ run
br-parse _ Γ | just _ | ParseTree (parsed-term t) :: [] = br-spans (set-ctxt Γ ≫span erased-spans t)
br-parse input Γ | just _ | _ = parse-error-message input "term"
br-parse input Γ | _ = parse-error-message input "term"

br-cmd : ctxt → (input : string) → (filename : string) → (local-ctxt : 𝕃 string) → string × 𝔹
br-cmd Γ input fn lc = br-parse (pretty-string input) (ctxt-set-current-file (merge-lcis-ctxt (strings-to-lcis lc) tt (ctxt-set-current-file Γ "missing")) "missing")

{- Conversion -}

conv-runs : ctxt → (span-run : Run) → (input-run : Run) → 𝔹
conv-runs Γ (ParseTree (parsed-term t₁) :: []) (ParseTree (parsed-term t₂) :: []) = conv-term Γ t₁ t₂
conv-runs _ _ _ = ff

conv-parse-try : 𝕃 char → 𝕃 char → 𝕃 gratr2-nt → maybe (Run × Run)
conv-parse-try s₁ s₂ (h :: t) with parse-specific-nt h 0 s₁ | parse-specific-nt h 0 s₂
conv-parse-try _ _ (h :: t) | (inj₂ r₁) | (inj₂ r₂) = just (rewriteRun r₁ , rewriteRun r₂)
conv-parse-try s₁ s₂ (h :: t) | _ | _ = conv-parse-try s₁ s₂ t
conv-parse-try _ _ [] = nothing

get-conv : ctxt → (span-str : string) → (input-str : string) → string
get-conv Γ ss is with conv-parse-try (string-to-𝕃char ss) (string-to-𝕃char is) try-nts
get-conv Γ ss is | just (sr , ir) = if conv-runs Γ sr ir then is else ss
get-conv Γ ss _ | nothing = ss

conv-cmd : ctxt → (span-str : string) → (input-str : string) → (start-pos : string) → (filename : string) → (local-ctxt : 𝕃 string) → string × 𝔹
conv-cmd _ _ _ sp _ _ with string-to-ℕ sp
conv-cmd Γ ss is _ fn lc | just sp = get-conv (get-local-ctxt Γ sp fn lc tt) (pretty-string ss) (pretty-string is) , tt
conv-cmd _ ss _ sp _ _ | nothing = parse-error-message sp "nat"

{- Commands -}

interactive-return : string × 𝔹 → IO ⊤
interactive-return (str , tt) = putStrLn (escape-string str)
interactive-return (str , ff) = putStrLn ("§" ^ (escape-string str))

interactive-cmd : 𝕃 string → ctxt → IO ⊤
interactive-cmd-h : ctxt → 𝕃 string → string × 𝔹
interactive-cmd ls Γ = interactive-return (interactive-cmd-h Γ ls)

interactive-cmd-h Γ ("normalize" :: input :: ll :: sp :: fn :: head :: do-erase :: lc) =
  normalize-cmd Γ input ll sp fn head do-erase lc
interactive-cmd-h Γ ("erase" :: input :: sp :: fn :: lc) = erase-cmd Γ input sp fn lc
interactive-cmd-h Γ ("normalizePrompt" :: input :: fn :: head :: []) = normalize-prompt-cmd Γ input fn head
interactive-cmd-h Γ ("erasePrompt" :: input :: fn :: []) = erase-prompt Γ input fn
interactive-cmd-h Γ ("br" :: input :: fn :: lc) = br-cmd Γ input fn lc
interactive-cmd-h Γ ("conv" :: ss :: is :: sp :: fn :: lc) = conv-cmd Γ ss is sp fn lc
interactive-cmd-h Γ cs = "Invalid interactive command sequence " ^ (𝕃-to-string (λ s → s) ", " cs) , ff
