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
open import erased-spans

{- General -}

parse-specific-nt : gratr2-nt → ℕ → (lc : 𝕃 char) → maybe Run
parse-specific-nt nt starting-char-position lc with
  parse-filter lc lc [] [] (cedille-start nt) inj₁
...| inj₁ _ = nothing
...| inj₂ run = just (rewriteRun (re-to-run starting-char-position (reverse run)))

parse-try-nts : 𝕃 char → 𝕃 gratr2-nt → maybe Run
parse-try-nts _ [] = nothing
parse-try-nts lc (h :: t) with parse-specific-nt h 0 lc
...| nothing = parse-try-nts lc t
...| just run = just run

try-nts : 𝕃 gratr2-nt
try-nts = (gratr2-nt._term :: gratr2-nt._type :: gratr2-nt._kind :: [])

var-is-type : ctxt → var → 𝔹
var-is-type Γ v with ctxt-lookup-term-var Γ v | ctxt-lookup-term-var-def Γ v |
                     ctxt-lookup-type-var Γ v | ctxt-lookup-type-var-def Γ v 
...| t-decl | t-def | T-decl | T-def = (isJust T-decl || isJust T-def) &&
                                     ~ (isJust t-decl || isJust t-def)

ll-disambiguate : ctxt → term → maybe cedille-types.type
ll-disambiguate Γ (Var pi v) with var-is-type Γ v
...| tt = just (TpVar pi v)
...| ff = nothing
ll-disambiguate Γ (AppTp t T) with ll-disambiguate Γ t
...| just T' = just (TpApp T' T)
...| nothing = nothing
ll-disambiguate Γ _ = nothing

ll-disambiguate-run : ctxt → Run → Run
ll-disambiguate-run Γ r @ (ParseTree (parsed-term t) :: []) with ll-disambiguate Γ t
...| just T = ParseTree (parsed-type T) :: []
...| nothing = r
ll-disambiguate-run _ r = r

𝕃char-starts-with : 𝕃 char → 𝕃 char → 𝔹
𝕃char-starts-with (h1 :: t1) (h2 :: t2) = (h1 =char h2) && 𝕃char-starts-with t1 t2
𝕃char-starts-with [] (h :: t) = ff
𝕃char-starts-with _ _ = tt

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

string-to-nt : string → maybe gratr2-nt
string-to-nt "term" = just gratr2-nt._term
string-to-nt "type" = just gratr2-nt._type
string-to-nt "kind" = just gratr2-nt._kind
string-to-nt _ = nothing

nt-to-string : gratr2-nt → string
nt-to-string gratr2-nt._term = "term"
nt-to-string gratr2-nt._type = "type"
nt-to-string gratr2-nt._kind = "kind"
nt-to-string _ = "[error: invalid nonterminal (src/interactive-cmds.agda/nt-to-string)]"


{- Contextualization (I think that's the correct word?) -}

local-ctxt-item : Set
local-ctxt-item = string × string × string × string × string × string
-- language-level , name , value , type , filename , position

strings-to-lcis : 𝕃 string → 𝕃 local-ctxt-item
strings-to-lcis ss = strings-to-lcis-h ss []
  where
    strings-to-lcis-h : 𝕃 string → 𝕃 local-ctxt-item → 𝕃 local-ctxt-item
    strings-to-lcis-h (ll :: name :: val :: T :: filename :: pos :: t) items =
      strings-to-lcis-h t ((ll , name , val , T , filename , pos) :: items)
    strings-to-lcis-h _ items = items

get-term-from-run : Run → maybe cedille-types.term
get-type-from-run : Run → maybe cedille-types.type
get-kind-from-run : Run → maybe cedille-types.kind
get-term-from-run ((ParseTree (parsed-term t)) :: []) = just t
get-term-from-run _ = nothing
get-type-from-run ((ParseTree (parsed-type T)) :: []) = just T
get-type-from-run _ = nothing
get-kind-from-run ((ParseTree (parsed-kind k)) :: []) = just k
get-kind-from-run _ = nothing

ctxt-def-tree : ctxt → gratr2-nt → (maybe Run) → Run → var → string → posinfo → (do-erase : 𝔹) → ctxt
ctxt-def-tree Γ gratr2-nt._term (just val-run) T-run v fn pos de with
  get-term-from-run val-run | get-type-from-run T-run
...| just t | just T = ctxt-term-def pos globalScope v (if de then (erase-term t) else t) T (ctxt-clear-symbol (ctxt-clear-symbol Γ v) (fn # v))
...| _ | _ = Γ
ctxt-def-tree Γ gratr2-nt._type (just val-run) T-run v fn pos de with
  get-type-from-run val-run | get-kind-from-run T-run
...| just T | just k = ctxt-type-def pos globalScope v (if de then (erase-type T) else T) k (ctxt-clear-symbol (ctxt-clear-symbol Γ v) (fn # v))
...| _ | _ = Γ
ctxt-def-tree Γ gratr2-nt._term nothing T-run v fn pos de with get-type-from-run T-run
...| just T = ctxt-term-decl pos v T (ctxt-clear-symbol (ctxt-clear-symbol Γ v) (fn # v))
...| nothing = Γ
ctxt-def-tree Γ gratr2-nt._type nothing T-run v fn pos de with get-kind-from-run T-run
...| just k = ctxt-type-decl pos v (if de then (erase-kind k) else k) (ctxt-clear-symbol (ctxt-clear-symbol Γ v) (fn # v))
...| nothing = Γ
ctxt-def-tree Γ _ _ _ _ _ _ _ = Γ

ctxt-set-cur-file : ctxt → string → ctxt
ctxt-set-cur-file (mk-ctxt (_ , ps , q) ss is os) fn = mk-ctxt (fn , ps , q) ss is os

ctxt-def-run : gratr2-nt → maybe Run → maybe Run → var →
               string → posinfo → (do-erase : 𝔹) → ctxt → ctxt
ctxt-def-run nt (just val-run) (just T-run) v fn pos de Γ =
  ctxt-set-cur-file
    (ctxt-def-tree (ctxt-set-cur-file Γ fn) nt (just val-run) T-run v fn pos de)
    (ctxt-get-current-filename Γ)
ctxt-def-run nt nothing (just T-run) v fn pos de Γ =
  ctxt-set-cur-file
    (ctxt-def-tree (ctxt-set-cur-file Γ fn) nt nothing T-run v fn pos de)
    (ctxt-get-current-filename Γ)
ctxt-def-run _ _ _ _ _ _ _ Γ = Γ

merge-lci-ctxt-h : gratr2-nt → gratr2-nt → (name : string) → (value : string) →
                   (t-k : string) → string → string → (do-erase : 𝔹) → ctxt → ctxt
merge-lci-ctxt-h val-nt T-nt name val t-k fn pos de Γ with
  parse-specific-nt val-nt 0 (string-to-𝕃char val) |
  parse-specific-nt T-nt 0 (string-to-𝕃char t-k)
...| val-run | T-run = ctxt-def-run val-nt val-run T-run name fn pos de Γ

merge-lci-ctxt : local-ctxt-item → (do-erase : 𝔹) → ctxt → ctxt
merge-lci-ctxt ("term" , name , value , T , filename , pos) de Γ =
  merge-lci-ctxt-h gratr2-nt._term gratr2-nt._type name value T filename pos de Γ
merge-lci-ctxt ("type" , name , value , T , filename , pos) de Γ =
  merge-lci-ctxt-h gratr2-nt._type gratr2-nt._kind name value T filename pos de Γ
merge-lci-ctxt _ _ Γ = Γ

merge-lcis-ctxt : 𝕃 local-ctxt-item → (do-erase : 𝔹) → ctxt → ctxt
merge-lcis-ctxt (h :: t) de Γ = merge-lcis-ctxt t de (merge-lci-ctxt h de Γ)
merge-lcis-ctxt [] _ Γ = Γ
    
to-nyd-h : trie sym-info → string → ℕ → (so-far : 𝕃 (sym-info × string)) →
           (path : 𝕃 char) → 𝕃 (sym-info × string)
to-nyd-h (Node msi ((c , h) :: t)) fn pos sf path =
  to-nyd-h (Node msi t) fn pos (to-nyd-h h fn pos sf (c :: path)) path
to-nyd-h (Node (just (ci , fp , pi)) []) fn pos sf path =
  if (fp =string fn) && ((posinfo-to-ℕ pi) > pos)
    then (((ci , fp , pi) , (𝕃char-to-string (reverse path))) :: sf)
    else sf
to-nyd-h _ _ _ sf _ = sf

to-nyd : trie sym-info → (filename : string) → (pos : ℕ) → 𝕃 (sym-info × string)
to-nyd tr fn pos = to-nyd-h tr fn pos [] []

ctxt-at : (pos : ℕ) → (filename : string) → ctxt → ctxt
ctxt-at pos filename Γ @ (mk-ctxt _ _ si _) =
  ctxt-nyd-all (ctxt-set-cur-file Γ filename) (to-nyd si filename pos)
  where
    ctxt-nyd-all : ctxt → 𝕃 (sym-info × string) → ctxt
    ctxt-nyd-all Γ (((_ , (fn , _)) , v) :: t) = ctxt-nyd-all (ctxt-clear-symbol (ctxt-clear-symbol Γ v) (fn # v)) t
    ctxt-nyd-all Γ [] = Γ

get-local-ctxt : ctxt → (pos : ℕ) → (filename : string) →
                 (local-ctxt : 𝕃 string) → (do-erase : 𝔹) → ctxt
get-local-ctxt Γ pos filename local-ctxt de =
  merge-lcis-ctxt (strings-to-lcis local-ctxt) de (ctxt-at pos filename Γ)

{- Normalization -}

normalize-tree : ctxt → (input : string) → Run → 𝔹 → string × 𝔹
normalize-tree Γ input (ParseTree (parsed-term t) :: []) head =
  to-string Γ (hnf Γ (unfold (~ head) ff ff) (qualif-term Γ t) tt) , tt
normalize-tree Γ input (ParseTree (parsed-type T) :: []) head =
  to-string Γ (hnf Γ (unfold (~ head) ff ff) (qualif-type Γ T) tt) , tt
normalize-tree Γ input (ParseTree (parsed-kind k) :: []) head =
  to-string Γ (hnf Γ (unfold (~ head) ff ff) (qualif-kind Γ k) tt) , tt
normalize-tree _ input _ _ = "\"" ^ input ^ "\" was not parsed as a term, type, or kind"  , ff

normalize-span : ctxt → (input : string) → gratr2-nt → (start-pos : ℕ) → (head : 𝔹) → string × 𝔹 
normalize-span Γ input nt sp head with parse-specific-nt nt sp (string-to-𝕃char input)
...| just run = normalize-tree Γ input run head
...| nothing = parse-error-message input (nt-to-string nt)

normalize-cmd : ctxt → (span : string) → string → (start-pos : string) → (filename : string) →
                (head : string) → (do-erase : string) → 𝕃 string → string × 𝔹
normalize-cmd Γ span ll sp fn hd de lc with
  string-to-nt ll | string-to-ℕ sp | string-to-𝔹 hd | string-to-𝔹 de
...| just ll' | just sp' | just hd' | just de' =
  normalize-span (get-local-ctxt Γ sp' fn lc de') (pretty-string span) ll' sp' hd'
...| nothing | _ | _ | _ = parse-error-message ll "language-level"
...| _ | nothing | _ | _ = parse-error-message sp "nat"
...| _ | _ | nothing | _ = parse-error-message hd "boolean"
...| _ | _ | _ | nothing = parse-error-message de "boolean"

normalize-prompt : ctxt → (input : string) → (head : 𝔹) → string × 𝔹
normalize-prompt Γ input head with parse-try-nts (string-to-𝕃char input) try-nts
...| nothing = parse-error-message input "term, type, or kind"
...| just run with normalize-tree Γ input (ll-disambiguate-run Γ run) head
...| s , tt = s , tt
...| error = error

normalize-prompt-cmd : ctxt → (input : string) → (filename : string) →
                       (head : string) → string × 𝔹
normalize-prompt-cmd Γ input fn head with string-to-𝔹 head
...| just hd = normalize-prompt (ctxt-set-cur-file Γ fn) (pretty-string input) hd
...| nothing = parse-error-message head "boolean"


{- Erasure -}

erase-tree : ctxt → (input : string) → Run → string × 𝔹
erase-tree Γ input (ParseTree (parsed-term t) :: []) = to-string Γ (erase-term (qualif-term Γ t)) , tt
erase-tree Γ input (ParseTree (parsed-type T) :: []) = to-string Γ (erase-type (qualif-type Γ T)), tt
erase-tree Γ input (ParseTree (parsed-kind k) :: []) = to-string Γ (erase-kind (qualif-kind Γ k)) , tt
erase-tree _ input _ = parse-error-message input "term, type, or kind"

erase-span : ctxt → (input : string) → gratr2-nt → (start-pos : ℕ) → string × 𝔹
erase-span Γ input nt sp with parse-specific-nt nt sp (string-to-𝕃char input)
...| just run = erase-tree Γ input run
...| nothing_ = parse-error-message input (nt-to-string nt)

erase-cmd : ctxt → (input : string) → string → (start-pos : string) →
            (filename : string) → (local-ctxt : 𝕃 string) → string × 𝔹
erase-cmd Γ input ll sp fn lc with string-to-ℕ sp | string-to-nt ll
...| just sp' | just nt' = erase-span (get-local-ctxt Γ sp' fn lc ff) (pretty-string input) nt' sp'
...| nothing | _ = parse-error-message sp "nat"
...| _ | nothing = parse-error-message ll "language-level"

erase-prompt-h : ctxt → (input : string) → maybe Run → string × 𝔹
erase-prompt-h Γ input (just run) with erase-tree Γ input (ll-disambiguate-run Γ run)
...| s , tt = s , tt
...| error = error
erase-prompt-h _ input nothing = parse-error-message input "term, type, or kind"

erase-prompt : ctxt → (input : string) → (filename : string) → string × 𝔹
erase-prompt Γ input fn with pretty-string-h (string-to-𝕃char input) []
...| lc = erase-prompt-h (ctxt-set-cur-file Γ fn) (𝕃char-to-string lc) (parse-try-nts lc try-nts)


{- Beta reduction -}

br-spans : spanM ⊤ → string × 𝔹
br-spans sM with snd (snd (sM empty-ctxt (regular-spans [])))
...| global-error error ms = error , ff
...| ss = spans-to-string ss , tt

br-parse : (input : string) → ctxt → string × 𝔹
br-parse input Γ with parse-try-nts (string-to-𝕃char input) try-nts
...| nothing = parse-error-message input "term, type, or kind"
...| just run with ll-disambiguate-run Γ run
...| ParseTree (parsed-term t) :: [] = br-spans (set-ctxt Γ ≫span erased-term-spans t)
...| ParseTree (parsed-type T) :: [] = br-spans (set-ctxt Γ ≫span erased-type-spans T)
...| ParseTree (parsed-kind k) :: [] = br-spans (set-ctxt Γ ≫span erased-kind-spans k)
...| _ = parse-error-message input "term, type, or kind"

br-cmd : ctxt → (input : string) → (filename : string) → (local-ctxt : 𝕃 string) → string × 𝔹
br-cmd Γ input fn lc = br-parse (pretty-string input) (ctxt-set-cur-file
  (merge-lcis-ctxt (strings-to-lcis lc) tt (ctxt-set-cur-file Γ "missing")) "missing")


{- Conversion -}

conv-runs : ctxt → (span-run : Run) → (input-run : Run) → 𝔹
conv-runs Γ (ParseTree (parsed-term t₁) :: []) (ParseTree (parsed-term t₂) :: []) =
  conv-term Γ (qualif-term Γ t₁) (qualif-term Γ t₂)
conv-runs Γ (ParseTree (parsed-type T₁) :: []) (ParseTree (parsed-type T₂) :: []) =
  conv-type Γ (qualif-type Γ T₁) (qualif-type Γ T₂)
conv-runs Γ (ParseTree (parsed-kind k₁) :: []) (ParseTree (parsed-kind k₂) :: []) =
  conv-kind Γ (qualif-kind Γ k₁) (qualif-kind Γ k₂)
conv-runs _ _ _ = ff

conv-disambiguate : ctxt → Run → Run → 𝔹
conv-disambiguate Γ r₁ r₂ =
  conv-runs Γ (ll-disambiguate-run Γ r₁) (ll-disambiguate-run Γ r₂)

conv-parse-try : 𝕃 char → 𝕃 char → gratr2-nt → (Run × Run) ⊎ string
conv-parse-try s₁ s₂ nt with parse-specific-nt nt 0 s₁ | parse-specific-nt nt 0 s₂
...| (just r₁) | (just r₂) = inj₁ (r₁ , r₂)
...| nothing | _ = inj₂ (𝕃char-to-string s₁)
...| _ | nothing = inj₂ (𝕃char-to-string s₂)

get-conv : ctxt → gratr2-nt → (span-str : string) → (input-str : string) → string × 𝔹
get-conv Γ nt ss is with conv-parse-try (string-to-𝕃char ss) (string-to-𝕃char is) nt
...| inj₁ (sr , ir) = (if conv-disambiguate Γ sr ir then is else ss) , tt
...| inj₂ s = parse-error-message s (nt-to-string nt)

conv-cmd : ctxt → string → (span-str : string) → (input-str : string) → (start-pos : string) →
           (filename : string) → (local-ctxt : 𝕃 string) → string × 𝔹
conv-cmd Γ ll ss is sp fn lc with string-to-ℕ sp | string-to-nt ll
...| just sp' | just nt' = get-conv (get-local-ctxt Γ sp' fn lc tt) nt' (pretty-string ss) (pretty-string is)
...| nothing | _ = parse-error-message sp "nat"
...| _ | nothing = parse-error-message ll "language-level"

{- Commands -}

interactive-return : string × 𝔹 → IO ⊤
interactive-return (str , tt) = putStrLn (escape-string str)
interactive-return (str , ff) = putStrLn ("§" ^ (escape-string str))

interactive-cmd : 𝕃 string → toplevel-state → IO toplevel-state
interactive-cmd-h : ctxt → 𝕃 string → string × 𝔹
interactive-cmd ls ts = interactive-return (interactive-cmd-h (toplevel-state.Γ ts) ls) >>
  return ts

interactive-cmd-h Γ ("normalize" :: input :: ll :: sp :: fn :: head :: do-erase :: lc) =
  normalize-cmd Γ input ll sp fn head do-erase lc
interactive-cmd-h Γ ("erase" :: input :: ll :: sp :: fn :: lc) =
  erase-cmd Γ input ll sp fn lc
interactive-cmd-h Γ ("normalizePrompt" :: input :: fn :: head :: []) =
  normalize-prompt-cmd Γ input fn head
interactive-cmd-h Γ ("erasePrompt" :: input :: fn :: []) =
  erase-prompt Γ input fn
interactive-cmd-h Γ ("br" :: input :: fn :: lc) =
  br-cmd Γ input fn lc
interactive-cmd-h Γ ("conv" :: ll :: ss :: is :: sp :: fn :: lc) =
  conv-cmd Γ ll ss is sp fn lc
interactive-cmd-h Γ cs =
  "Invalid interactive command sequence " ^ (𝕃-to-string (λ s → s) ", " cs) , ff

