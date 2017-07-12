module interactive-cmds where

open import cedille
open import conversion
open import ctxt
open import general-util
-- open import maybe
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

get-si : ctxt → trie sym-info
get-si (mk-ctxt _ _ si _) = si

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
local-ctxt-item = string × string × string -- language-level , name , value

make-local-ctxt-item : 𝕃 string → local-ctxt-item
make-local-ctxt-item (lang-level :: name :: value :: []) = lang-level , name , value
make-local-ctxt-item _ = "" , "" , ""

strings-to-lcis-h : 𝕃 string → 𝕃 local-ctxt-item → 𝕃 local-ctxt-item
strings-to-lcis-h (h :: t) items =
  strings-to-lcis-h t ((make-local-ctxt-item (string-split h '⦀')) :: items)
strings-to-lcis-h [] items = items

strings-to-lcis : 𝕃 string → 𝕃 local-ctxt-item
strings-to-lcis ss = strings-to-lcis-h ss []

get-term-from-run : Run → term
get-term-from-run ((ParseTree (parsed-term t)) :: []) = t
get-term-from-run _ = Var "0" "error-at-get-term-from-run"

get-type-from-run : Run → type
get-type-from-run ((ParseTree (parsed-type t)) :: []) = t
get-type-from-run _ = TpVar "0" "error-at-get-type-from-run"

merge-lci-ctxt-h : (name : string) → (value : string) → gratr2-nt → ctxt → ctxt
merge-lci-ctxt-h name value nt Γ = return-run nt (parse-specific-nt nt 0 (string-to-𝕃char name)) name Γ
  where
    return-tree : gratr2-nt → Run → var → ctxt → ctxt
    return-tree gratr2-nt._term run v c = ctxt-term-udef "0" v (get-term-from-run run) c
    return-tree gratr2-nt._type run v c = ctxt-type-udef "0" v (get-type-from-run run) c
    return-tree _ _ _ c = c
    return-run : gratr2-nt → 𝕃 char ⊎ Run → var → ctxt → ctxt
    return-run _ (inj₁ _) _ c = c
    return-run nt (inj₂ run) v c = return-tree nt (rewriteRun run) v c

merge-lci-ctxt : local-ctxt-item → ctxt → ctxt
merge-lci-ctxt ("term" , name , value) = merge-lci-ctxt-h name value gratr2-nt._term
merge-lci-ctxt ("type" , name , value) = merge-lci-ctxt-h name value gratr2-nt._type
merge-lci-ctxt _ Γ = Γ

merge-lcis-ctxt : 𝕃 local-ctxt-item → ctxt → ctxt
merge-lcis-ctxt ((ll , name , value) :: t) Γ = merge-lcis-ctxt t (if ctxt-defines-var Γ name then (merge-lci-ctxt (ll , name , value) Γ) else Γ)
merge-lcis-ctxt [] Γ = Γ

-- merge-strings-ctxt : 𝕃 string → ctxt → ctxt
-- merge-strings-ctxt ss Γ =  merge-lcis-ctxt (strings-to-lcis ss) Γ

is-nyd : sym-info → (filename : string) → (pos : ℕ) → 𝔹
is-nyd (ci , (fp , pi)) fn pos = (fp =string fn) && ((posinfo-to-ℕ pi) > pos)

to-nyd-h : trie sym-info → (filename : string) → (pos : ℕ) → (so-far : 𝕃 (sym-info × string)) → (path : 𝕃 char) → 𝕃 (sym-info × string)
to-nyd-h (Node msi ((c , h) :: t)) fn pos sf path = to-nyd-h (Node msi t) fn pos (to-nyd-h h fn pos sf (c :: path)) path
to-nyd-h (Node (just si) []) fn pos sf path = if is-nyd si fn pos then ((si , (𝕃char-to-string (reverse path))) :: sf) else sf
to-nyd-h _ _ _ sf _ = sf

to-nyd : trie sym-info → (filename : string) → (pos : ℕ) → 𝕃 (sym-info × string)
to-nyd tr fn pos = to-nyd-h tr fn pos [] []

ctxt-nyd : ctxt → sym-info × string → ctxt
ctxt-nyd Γ (((term-decl typ)     , (fp , pi)) , v) = ctxt-term-udef pi v (Var pi v) Γ
ctxt-nyd Γ (((term-def trm typ)  , (fp , pi)) , v) = ctxt-term-udef pi v (Var pi v) Γ
ctxt-nyd Γ (((term-udef trm)     , (fp , pi)) , v) = ctxt-term-udef pi v (Var pi v) Γ
ctxt-nyd Γ (((type-decl knd)     , (fp , pi)) , v) = ctxt-type-udef pi v (TpVar pi v) Γ
ctxt-nyd Γ (((type-def typ knd)  , (fp , pi)) , v) = ctxt-type-udef pi v (TpVar pi v) Γ
ctxt-nyd Γ (((type-udef typ)     , (fp , pi)) , v) = ctxt-type-udef pi v (TpVar pi v) Γ
ctxt-nyd Γ (((kind-def prms knd) , (fp , pi)) , v) = ctxt-kind-def  pi v ParamsNil (KndVar pi v (ArgsNil pi)) Γ
ctxt-nyd Γ (((rename-def vr)     , (fp , pi)) , v) = ctxt-rename    pi v v Γ
ctxt-nyd Γ (((rec-def typ knd)   , (fp , pi)) , v) = ctxt-rec-def   pi v (TpVar pi v) (KndVar pi v (ArgsNil pi)) Γ
ctxt-nyd Γ ((var-decl            , (fp , pi)) , v) = ctxt-rename    pi v v Γ

ctxt-nyd-all : ctxt → 𝕃 (sym-info × string) → ctxt
ctxt-nyd-all Γ (h :: t) = ctxt-nyd-all (ctxt-nyd Γ h) t
ctxt-nyd-all Γ [] = Γ

ctxt-at : (pos : ℕ) → (filename : string) → ctxt → ctxt
ctxt-at pos filename Γ = ctxt-nyd-all Γ (to-nyd (get-si Γ) filename pos)

get-local-ctxt : (pos : ℕ) → (filename : string) → (local-ctxt : 𝕃 string) → ctxt → ctxt
get-local-ctxt pos filename local-ctxt Γ = merge-lcis-ctxt (strings-to-lcis local-ctxt) (ctxt-at pos filename Γ)





{- Normalize code -}

normalize-tree : ctxt → (input : string) → Run → 𝔹 → string × 𝔹
normalize-tree Γ input (ParseTree (parsed-term t) :: []) full = (to-string (hnf Γ (unfold full ff ff) t tt)) , tt
normalize-tree Γ input (ParseTree (parsed-type t) :: []) full = (to-string (hnf Γ (unfold full ff ff) t tt)) , tt
normalize-tree _ input  _ _ = input , ff

normalize-Run-or-error : ctxt → (input : string) → 𝕃 char ⊎ Run → 𝔹 → string × 𝔹
normalize-Run-or-error _ input (inj₁ chars) full = input , ff
normalize-Run-or-error Γ input (inj₂ run) full = normalize-tree Γ input (rewriteRun run) full

normalize-span : ctxt → gratr2-nt → string → ℕ → 𝔹 → string × 𝔹 
normalize-span Γ nt text sp full = normalize-Run-or-error Γ text (parse-specific-nt nt sp (string-to-𝕃char text)) full

normalize-cmd-h : (start-pos : ℕ) → ctxt → gratr2-nt → (span-str : string) → (filename : string) → (full : string) → (local-ctxt : 𝕃 string) → string × 𝔹
normalize-cmd-h start-pos Γ nt str filename full local-ctxt = normalize-span (get-local-ctxt start-pos filename local-ctxt Γ) nt str start-pos (string-to-𝔹 full)

normalize-cmd : (start-pos : ℕ) → (span-str : string) → ctxt → 𝕃 string → string × 𝔹
normalize-cmd start-pos span-str Γ ("term" :: filename :: full :: local-ctxt) =
  normalize-cmd-h start-pos Γ gratr2-nt._term span-str filename full local-ctxt
normalize-cmd start-pos span-str Γ ("type"  :: filename :: full :: local-ctxt) =
  normalize-cmd-h start-pos Γ gratr2-nt._type span-str filename full local-ctxt
normalize-cmd _ span-str _ _ = span-str , ff

choose-run : (term-run : 𝕃 char ⊎ Run) → (type-run : 𝕃 char ⊎ Run) → maybe Run
choose-run (inj₂ run) _ = just run
choose-run _ (inj₂ run) = just run
choose-run _ _ = nothing

normalize-just-run : maybe Run → ctxt → (input : string) → (full : 𝔹) → string × 𝔹
normalize-just-run (just run) Γ input full = normalize-tree Γ input (rewriteRun run) full
normalize-just-run nothing _ input _ = input , ff

normalize-prompt : (input : string) → ctxt → (full : 𝔹) → string × 𝔹
normalize-prompt input _ _ with string-to-𝕃char input
normalize-prompt input _ _ | chars with parse-specific-nt gratr2-nt._term 0 chars
normalize-prompt input _ _ | chars | _ with parse-specific-nt gratr2-nt._type 0 chars
normalize-prompt _ _ _ | _ | term-run | type-run with choose-run term-run type-run
normalize-prompt input Γ full | _ | _ | _ | just-run with normalize-just-run just-run Γ input full
normalize-prompt input _ full | _ | _ | _ | _ | (str , tt) = ("Expression: " ^ input ^ norm-str ^ str) , tt
  where norm-str = if full then "\nNormalized: " else "\nHead-normalized: "
normalize-prompt _ _ _ | _ | _ | _ | _ | error = error



{- Erasure code -}

erase-tree : ctxt → (input : string) → Run → string × 𝔹
erase-tree Γ input (ParseTree (parsed-term t) :: []) = (to-string (erase-term t)) , tt
erase-tree _ input _ = input , ff

erase-run : (input : string) → 𝕃 char ⊎ Run → ctxt → string × 𝔹
erase-run input (inj₁ _) Γ = input , ff
erase-run input (inj₂ run) Γ = erase-tree Γ input (rewriteRun run)

erase-span : ctxt → string → ℕ → string × 𝔹
erase-span Γ str start-pos = erase-run str (parse-specific-nt gratr2-nt._term start-pos (string-to-𝕃char str)) Γ

erase-cmd-h : (start-pos : ℕ) → ctxt → (span-str : string) → (filename : string) → (local-ctxt : 𝕃 string) → string × 𝔹
erase-cmd-h start-pos Γ str filename local-ctxt = erase-span (get-local-ctxt start-pos filename local-ctxt Γ) str start-pos

erase-cmd : (start-pos : ℕ) → (span-str : string) → ctxt → 𝕃 string → string × 𝔹
erase-cmd start-pos span-str Γ (filename :: local-ctxt) =
  erase-cmd-h start-pos Γ span-str filename local-ctxt
erase-cmd _ span-str _ _ = span-str , ff

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
interactive-return (str , ff) ts = putStrLn (global-error-string ("Error parsing \"" ^ str ^ "\"")) >>= λ _ → return ts

remove-ws : 𝕃 char → 𝕃 char
remove-ws (' ' :: lc) = lc 
remove-ws lc = lc

-- Makes the string more aesthetically pleasing by removing newlines,
-- replacing tabs with spaces, and removing unnecessary double whitespaces
pretty-string-h : 𝕃 char → 𝕃 char → 𝕃 char
pretty-string-h ('\n' :: rest) so-far = pretty-string-h rest (' ' :: remove-ws so-far)
pretty-string-h (' ' :: rest) so-far = pretty-string-h rest (' ' :: remove-ws so-far)
pretty-string-h ('\t' :: rest) so-far = pretty-string-h rest (' ' :: remove-ws so-far)
pretty-string-h (c :: rest) so-far = pretty-string-h rest (c :: so-far)
pretty-string-h [] so-far = reverse (remove-proceeding-ws-period so-far)
  where
    remove-proceeding-ws-period : 𝕃 char → 𝕃 char
    remove-proceeding-ws-period (' ' :: rest) = rest
    remove-proceeding-ws-period ('.' :: rest) = rest
    remove-proceeding-ws-period rest = rest

pretty-string : string → string
pretty-string str = 𝕃char-to-string (pretty-string-h (string-to-𝕃char str) [])

handle-span-cmd : (cmd-name : string) → (start-pos : ℕ) → (end-pos : ℕ) → (span-str : string) → ctxt → (rest : 𝕃 string) → string × 𝔹
handle-span-cmd "normalize" sp ep span-str Γ rest = normalize-cmd sp span-str Γ rest
handle-span-cmd "erase" sp ep span-str Γ rest = erase-cmd sp span-str Γ rest
handle-span-cmd unknown-cmd _ _ _ _ _ = "Unknown command \"" ^ unknown-cmd ^ "\"" , ff

interactive-span-cmd : (cmd-name : string) → (start-pos : string) → (end-pos : string) → (span-str : string) → (rest : 𝕃 string) → toplevel-state → IO toplevel-state
interactive-span-cmd cmd-name start-pos end-pos span-str rest ts =
  interactive-return (handle-span-cmd cmd-name sp ep str Γ rest) ts
  where
    str = pretty-string span-str
    Γ = ts-to-ctxt ts
    sp = posinfo-to-ℕ start-pos
    ep = posinfo-to-ℕ end-pos

interactive-prompt-cmd : (cmd-name : string) → (input : string) → (rest : 𝕃 string) → toplevel-state → IO toplevel-state
interactive-prompt-cmd "normalize" input (full :: []) ts =
  interactive-return (normalize-prompt (pretty-string input) (ts-to-ctxt ts) (string-to-𝔹 full)) ts
interactive-prompt-cmd "erase" input [] ts =
  interactive-return (erase-prompt (pretty-string input) (ts-to-ctxt ts)) ts
interactive-prompt-cmd cmd-name _ rest ts =
  putStrLn ("Unknown cmd \"" ^ cmd-name ^ "\" with arguments \"(" ^ (𝕃-to-string (λ x → x) ", " rest) ^ ")\"") >>= λ x → return ts
