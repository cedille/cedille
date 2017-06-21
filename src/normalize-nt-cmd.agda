module normalize-nt-cmd where

open import cedille
open import conversion
open import ctxt
open import general-util
open import syntax-util
open import to-string
open import toplevel-state

import parse
open import lib
open import cedille-types
-- import cedille

-- module parsem = parse cedille.gratr2-nt ptr
module parsem = parse gratr2-nt ptr
open parsem
-- open parsem.pnoderiv cedille.rrs cedille.cedille-rtn
open parsem.pnoderiv rrs cedille-rtn
open import run ptr
open noderiv {- from run.agda -}


{- Normalize command ("N") -}
parse-specific-nt : gratr2-nt → ℕ → (lc : 𝕃 char) → 𝕃 char ⊎ Run
parse-specific-nt nt starting-char-position lc with parse-filter lc lc [] [] (cedille-start nt) inj₁
...| inj₁ left = inj₁ left
...| inj₂ run = inj₂ (re-to-run starting-char-position (reverse run))

get-ctxt-from-toplevel-state : toplevel-state → ctxt
get-ctxt-from-toplevel-state (mk-toplevel-state _ _ _ _ context) = context

local-ctxt-item : Set
local-ctxt-item = string × string × string -- language-level , name , value

make-local-ctxt-item : 𝕃 string → local-ctxt-item
make-local-ctxt-item (lang-level :: name :: value :: []) = lang-level , name , value
make-local-ctxt-item _ = "" , "" , ""
strings-to-local-ctxt-items-h : 𝕃 string → 𝕃 local-ctxt-item → 𝕃 local-ctxt-item
strings-to-local-ctxt-items-h (h :: t) items =
  strings-to-local-ctxt-items-h t ((make-local-ctxt-item (string-split h '⦀')) :: items)
strings-to-local-ctxt-items-h [] items = items
strings-to-local-ctxt-items : 𝕃 string → 𝕃 local-ctxt-item
strings-to-local-ctxt-items ss = strings-to-local-ctxt-items-h ss []

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

merge-strings-ctxt : 𝕃 string → ctxt → ctxt
merge-strings-ctxt ss Γ =  merge-lcis-ctxt (strings-to-local-ctxt-items ss) Γ
is-nyd : sym-info → (filename : string) → (pos : ℕ) → 𝔹
is-nyd (ci , (fp , pi)) fn pos = path-eq && ((posinfo-to-ℕ pi) > pos)
  where
    starts-with : 𝕃 char → 𝕃 char → 𝔹
    starts-with (h :: t) (h' :: t') = if h =char h' then starts-with t t' else ff
    -- starts-with ('/' :: _) [] = tt
    starts-with [] [] = tt
    starts-with _ _ = ff
    path-eq = starts-with (reverse (string-to-𝕃char fp)) (reverse (string-to-𝕃char fn))

to-nyd-h : trie sym-info → (filename : string) → (pos : ℕ) → (so-far : 𝕃 (sym-info × string)) → (path : 𝕃 char) → 𝕃 (sym-info × string)
to-nyd-h (Node msi ((c , h) :: t)) fn pos sf path = to-nyd-h (Node msi t) fn pos (to-nyd-h h fn pos sf (c :: path)) path
to-nyd-h (Node (just si) []) fn pos sf path = if is-nyd si fn pos then ((si , (𝕃char-to-string (reverse path))) :: sf) else sf
to-nyd-h _ _ _ sf _ = sf
to-nyd : trie sym-info → (filename : string) → (pos : ℕ) → 𝕃 (sym-info × string)
to-nyd tr fn pos = to-nyd-h tr fn pos [] []

nyd-var : string → string -- Not Yet Declared
nyd-var v = v  -- "NYD-" ^ v
-- Maybe eventually do something to indicate a variable has not yet been declared?

ctxt-nyd : ctxt → sym-info × string → ctxt
ctxt-nyd Γ (((term-decl typ)     , (fp , pi)) , v) = ctxt-term-udef pi v (Var pi (nyd-var v)) Γ
ctxt-nyd Γ (((term-def trm typ)  , (fp , pi)) , v) = ctxt-term-udef pi v (Var pi (nyd-var v)) Γ
ctxt-nyd Γ (((term-udef trm)     , (fp , pi)) , v) = ctxt-term-udef pi v (Var pi (nyd-var v)) Γ
ctxt-nyd Γ (((type-decl knd)     , (fp , pi)) , v) = ctxt-type-udef pi v (TpVar pi (nyd-var v)) Γ
ctxt-nyd Γ (((type-def typ knd)  , (fp , pi)) , v) = ctxt-type-udef pi v (TpVar pi (nyd-var v)) Γ
ctxt-nyd Γ (((type-udef typ)     , (fp , pi)) , v) = ctxt-type-udef pi v (TpVar pi (nyd-var v)) Γ
ctxt-nyd Γ (((kind-def prms knd) , (fp , pi)) , v) = ctxt-kind-def  pi v ParamsNil (KndVar pi (nyd-var v) (ArgsNil pi)) Γ
ctxt-nyd Γ (((rename-def vr)     , (fp , pi)) , v) = ctxt-rename    pi v (nyd-var v) Γ
ctxt-nyd Γ (((rec-def typ knd)   , (fp , pi)) , v) = ctxt-rec-def   pi v (TpVar pi (nyd-var v)) (KndVar pi (nyd-var v) (ArgsNil pi)) Γ
ctxt-nyd Γ ((var-decl            , (fp , pi)) , v) = ctxt-rename    pi v (nyd-var v) Γ
ctxt-nyd-all : ctxt → 𝕃 (sym-info × string) → ctxt
ctxt-nyd-all Γ (h :: t) = ctxt-nyd-all (ctxt-nyd Γ h) t
ctxt-nyd-all Γ [] = Γ

normalize-tree : ctxt → Run → string
normalize-tree Γ (ParseTree (parsed-term t) :: []) = to-string (hnf Γ unfold-all t tt)
normalize-tree Γ (ParseTree (parsed-type t) :: []) = to-string (hnf Γ unfold-all t tt)
normalize-tree _ _ = "error at normalize-tree"
normalize-Run-or-error : ctxt → 𝕃 char ⊎ Run → string
normalize-Run-or-error _ (inj₁ chars) = 𝕃char-to-string chars
normalize-Run-or-error Γ (inj₂ run) = normalize-tree Γ (rewriteRun run)

normalize-span : ctxt → gratr2-nt → string → ℕ → ℕ → string
normalize-span Γ nt text sp ep = (normalize-Run-or-error Γ (parse-specific-nt nt sp (string-to-𝕃char text))) ^ "§" ^ (ℕ-to-string sp) ^ "§" ^ (ℕ-to-string ep)

normalize-prompt : ctxt → string → string
normalize-prompt _ text with parse-specific-nt gratr2-nt._term 0 (string-to-𝕃char text)
normalize-prompt Γ text | (inj₂ run) = "Expression: " ^ text ^ "\nNormalized: " ^ (normalize-tree Γ (rewriteRun run))
normalize-prompt _ text | (inj₁ _) with (parse-specific-nt gratr2-nt._type 0 (string-to-𝕃char text))
normalize-prompt Γ text | (inj₁ _) | (inj₂ run) = text ^ " → " ^ (normalize-tree Γ (rewriteRun run))
normalize-prompt Γ text | (inj₁ _) | (inj₁ _) =
  "Failure parsing \"" ^ text ^ "\" (make sure the input is a term or a type, and that there no there are no typos)."

get-si : ctxt → trie sym-info
get-si (mk-ctxt _ _ si _) = si

normalize-cmd-h : 𝕃 string → toplevel-state → gratr2-nt → string
normalize-cmd-h (str :: start-pos :: end-pos :: filename :: local-ctxt) (mk-toplevel-state _ _ _ _ Γ) nt =
  (normalize-span c' nt str sp ep)
  where
    sp = posinfo-to-ℕ start-pos
    ep = posinfo-to-ℕ end-pos
    lss = to-nyd (get-si Γ) filename sp
    c = ctxt-nyd-all Γ lss
    c' = merge-strings-ctxt local-ctxt c
normalize-cmd-h _ _ _ = "Error! (normalize-nt-cmd.agda/normalize-cmd-h)"

normalize-cmd : 𝕃 string → toplevel-state → string
normalize-cmd(text :: []) (mk-toplevel-state _ _ _ _ Γ) = (normalize-prompt Γ text)
normalize-cmd ("term" :: rest) ts = normalize-cmd-h rest ts gratr2-nt._term
normalize-cmd ("type" :: rest) ts = normalize-cmd-h rest ts gratr2-nt._type
-- Errors
normalize-cmd (lang-level :: _) _ = "Unknown language-level \"" ^ lang-level ^ "\" (normalize-nt-cmd.agda/normalize-cmd)"
normalize-cmd [] _ = "0 string arguements passed to normalize-nt-cmd.agda/normalize-cmd"
