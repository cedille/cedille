module main where

import parse
open import lib
open import cedille-types
import cedille

module parsem = parse cedille.gratr2-nt ptr
open parsem
open parsem.pnoderiv cedille.rrs cedille.cedille-rtn
open import run ptr
open noderiv {- from run.agda -}

open import classify
open import ctxt
open import constants
open import conversion
open import rec
open import spans
open import syntax-util
open import to-string

-- keep track of our includes
data include-state : Set where
  mk-include-state : trie start → stringset {- processed -} → stringset {- unchanged -} → include-state

new-include-state : trie start → stringset → include-state
new-include-state asts unchanged = mk-include-state asts empty-stringset unchanged

data toplevel-state : Set where
  mk-toplevel-state : include-state → ctxt → spans → toplevel-state

new-toplevel-state : (current-file : string) → trie start → stringset → toplevel-state
new-toplevel-state file-name asts unchanged = mk-toplevel-state (new-include-state asts unchanged) (new-ctxt file-name) empty-spans

new-toplevel-global-error : (current-file : string) → string → toplevel-state
new-toplevel-global-error file-name m = 
  mk-toplevel-state (new-include-state empty-trie empty-stringset) (new-ctxt file-name) (global-error m nothing)

toplevel-add-span : span → toplevel-state → toplevel-state
toplevel-add-span s (mk-toplevel-state is Γ ss) =
  mk-toplevel-state is Γ (add-span s ss)

dot-cedille-directory : string → string 
dot-cedille-directory dir = combineFileNames dir ".cedille"

cede-filename : string → string → string
cede-filename dir base = combineFileNames (dot-cedille-directory dir) (base ^ ".cede")

write-cede-file : string → string → string → IO ⊤
write-cede-file dir base contents = 
  createDirectoryIfMissing ff (dot-cedille-directory dir) >>
  writeFile (cede-filename dir base) contents   

add-cedille-extension : string → string
add-cedille-extension x = x ^ "." ^ cedille-extension 

postulate 
  test : IO 𝔹

{-# COMPILED test (return True) #-}

ced-file-up-to-date : (dir : string) → (file : string) → IO 𝔹
ced-file-up-to-date dir file =
  let base = base-filename file in
  let e = cede-filename dir base in
  let f = combineFileNames dir file in
    doesFileExist e >>= λ b → 
    if b then
      fileIsOlder f e
    else
      return ff

{- these are mutually recursive due to Import commands.
   dir is the directory to search for includes (we should 
   add a more sophisticated mechanism later) -}

{-# NO_TERMINATION_CHECK #-}
process-cmd : (dir : string) → cmd → (no-need-to-check : 𝔹) → toplevel-state → IO toplevel-state
process-cmds : (dir : string) → cmds → (no-need-to-check : 𝔹) → toplevel-state → IO toplevel-state
process-start : (dir : string) → start → (no-need-to-check : 𝔹) → toplevel-state → IO toplevel-state
processFile : (dir : string) → (file : string) → toplevel-state → IO (𝔹 × toplevel-state) -- the boolean is for if there was an error

process-cmd dir (DefTerm pi x (Type tp) t n pi') ff {- should check -} (mk-toplevel-state is Γ ss) = 
  let ss' = (check-type Γ tp (just star) ≫span 
             check-term Γ t (just tp) ≫span 
             let t = erase-term t in
               spanM-add (DefTerm-span pi x tt (just tp) t pi' (normalized-term-if Γ n t)) ≫span 
               spanMr (hnf Γ unfold-head t)) ss in
    return (mk-toplevel-state is (ctxt-term-def pi x (fst ss') tp Γ) (snd ss'))

process-cmd dir (DefTerm pi x (Type tp) t n pi') tt {- skip checking -} (mk-toplevel-state is Γ ss) = 
    return (mk-toplevel-state is (ctxt-term-def pi x (hnf Γ unfold-head t) tp Γ) ss)

process-cmd dir (DefTerm pi x NoCheckType t n pi') _ (mk-toplevel-state is Γ ss) = 
  let ss' = (check-term Γ t nothing ≫=span λ mtp → 
             let t = erase-term t in
               spanM-add (DefTerm-span pi x ff mtp t pi' (normalized-term-if Γ n t)) ≫span
               spanMr (hnf Γ unfold-head t , mtp)) ss in
    return (mk-toplevel-state is (h (fst ss')) (snd ss'))
  where h : term × (maybe type) → ctxt
        h (t , nothing) = ctxt-term-udef pi x t Γ
        h (t , just tp) = ctxt-term-def pi x t tp Γ

process-cmd dir (DefType pi x (Kind k) tp n pi') ff {- check -} (mk-toplevel-state is Γ ss) = 
  let ss' = (check-kind Γ k ≫span 
             check-type Γ tp (just k) ≫span 
               spanM-add (DefType-span pi x tt (just k) tp pi' (normalized-type-if Γ n tp)) ≫span 
               spanMr (hnf Γ unfold-head tp)) ss in
    return (mk-toplevel-state is (ctxt-type-def pi x (fst ss') k Γ) (snd ss'))
process-cmd dir (DefType pi x (Kind k) tp n pi') tt {- skip checking -} (mk-toplevel-state is Γ ss) = 
  return (mk-toplevel-state is (ctxt-type-def pi x (hnf Γ unfold-head tp) k Γ) ss)

process-cmd dir (CheckTerm t (Type tp) n pi) ff {- check -} (mk-toplevel-state is Γ ss) = 
  let ss' = (check-type Γ tp (just star) ≫span 
             check-term Γ t (just tp) ≫span 
             let t = erase-term t in
               spanM-add (CheckTerm-span tt (just tp) t pi (normalized-term-if Γ n t)) ≫span 
               spanMok) ss in
    return (mk-toplevel-state is Γ (snd ss'))
process-cmd dir (CheckTerm t _ n pi) tt {- skip checking -} s = return s

process-cmd dir (CheckTerm t NoCheckType n pi) ff {- check -} (mk-toplevel-state is Γ ss) = 
  let ss' = (check-term Γ t nothing ≫=span λ m → 
               spanM-add (CheckTerm-span ff m t pi (normalized-term-if Γ n t)) ≫span 
               spanMok) ss in
    return (mk-toplevel-state is Γ (snd ss'))

process-cmd dir (CheckType tp m n pi) _ (mk-toplevel-state is Γ ss) = 
  return (mk-toplevel-state is Γ ss)

process-cmd dir (DefKind pi x _ k pi') ff {- check -} (mk-toplevel-state is Γ ss) = 
  let ss' = (check-kind Γ k ≫span
             spanM-add (DefKind-span pi x k pi') ≫span
             spanMok) ss in
  return (mk-toplevel-state is (ctxt-kind-def pi x (hnf Γ unfold-head k) Γ) (snd ss'))
process-cmd dir (DefKind pi x _ k pi') tt {- skip checking -} (mk-toplevel-state is Γ ss) = 
  return (mk-toplevel-state is (ctxt-kind-def pi x (hnf Γ unfold-head k) Γ) ss)

process-cmd dir (CheckKind k _ pi) _ (mk-toplevel-state is Γ ss) = 
  return (mk-toplevel-state is Γ ss)
process-cmd dir (Import pi x pi') _ s with toplevel-add-span (Import-span pi x pi' []) s
process-cmd dir (Import pi x pi') _ _ | s with s
process-cmd dir (Import pi x pi') _ _ | s | mk-toplevel-state (mk-include-state asts processed unchanged) Γ _ = 
  let file = add-cedille-extension x in
    if stringset-contains processed (combineFileNames dir file) then return s
    else 
      (processFile dir file s >>= cont)
  where cont : 𝔹 × toplevel-state → IO toplevel-state
        cont (b , s) with s 
        cont (b , s) | mk-toplevel-state i Γ' _ = 
          if b then
            return (toplevel-add-span (Import-span pi x pi' [ error-data "There is an error in the imported file" ]) s)
          else return s
       
process-cmd dir (Rec pi pi'' name params inds ctors body us pi') no-need-to-check (mk-toplevel-state i Γ ss) = 
    let p = process-rec-cmd no-need-to-check Γ pi pi'' name params inds ctors body us pi' ss in
    return (mk-toplevel-state i (fst p) (snd p))

process-cmds dir (CmdsNext c cs) no-need-to-check s = process-cmd dir c no-need-to-check s >>= cont
  where cont : toplevel-state → IO toplevel-state
        cont s with s 
        cont s | (mk-toplevel-state i c ss) = 
          if global-error-p ss then return s else process-cmds dir cs no-need-to-check s
process-cmds dir (CmdsStart c) no-need-to-check s = process-cmd dir c no-need-to-check s

process-start dir (File pi cs pi') no-need-to-check (mk-toplevel-state is Γ ss) = 
  process-cmds dir cs no-need-to-check (mk-toplevel-state is Γ ss) >>=
    λ s' → return (toplevel-add-span (File-span pi (posinfo-plus pi' 1) (ctxt-get-current-file Γ)) s')

-- process the given input file, after adding it to the include state
processFile dir file s with s | combineFileNames dir file
processFile dir file s | (mk-toplevel-state (mk-include-state asts processed unchanged) Γ ss) 
                       | input-filename with trie-lookup asts input-filename
processFile dir file s | (mk-toplevel-state (mk-include-state asts processed unchanged) Γ ss) 
                       | input-filename | nothing = 
    return (tt , mk-toplevel-state (mk-include-state asts processed unchanged) Γ
                   (global-error ("Internal error looking up ast for file " ^ input-filename ^ ".") nothing))
processFile dir file s | (mk-toplevel-state (mk-include-state asts processed unchanged) Γ ss) 
                       | input-filename | just p with stringset-contains unchanged input-filename
processFile dir file s | (mk-toplevel-state (mk-include-state asts processed unchanged) Γ ss) 
                       | input-filename | just p | skip-checking =
   let Γ' = ctxt-set-current-file Γ input-filename in 
--    putStr ("(current file in ctxt: " ^ (ctxt-get-current-file Γ') ^ "\n") >> 
    process-start dir p skip-checking
      (mk-toplevel-state (mk-include-state asts (stringset-insert processed input-filename) unchanged) 
          Γ' empty-spans)
   >>= finish
   where finish : toplevel-state → IO (𝔹 × toplevel-state)
         finish (mk-toplevel-state i Γ' ss') = 
          let Γ'' = ctxt-set-current-file Γ' (ctxt-get-current-file Γ) in 
--           putStr ("current file in ctxt: " ^ (ctxt-get-current-file Γ'') ^ ")\n") >>
           let base = base-filename file in
             (if skip-checking then (return triv) else (write-cede-file dir base (spans-to-string ss'))) >>
                -- do not return the newly added spans, unless we have a global error
             return (spans-have-error ss' , mk-toplevel-state i Γ'' (if global-error-p ss' then ss' else ss))

-- compute the set of unchanged dependencies (the second stringset in the include-state)
{-# NO_TERMINATION_CHECK #-}
compute-unchanged-imports : (dir : string) → cmds → include-state → IO ((𝔹 {- all imports unchanged -} × include-state) ⊎ string)
compute-unchanged : (dir : string) → (file : string) → include-state → IO (include-state ⊎ string)

compute-unchanged-imports dir (CmdsNext (Import _ x _) cs) is with add-cedille-extension x 
compute-unchanged-imports dir (CmdsNext (Import _ x _) cs) is | file = 
  compute-unchanged dir file is >>= cont
  where cont : include-state ⊎ string → IO ((𝔹 × include-state) ⊎ string)
        cont (inj₁ is') = compute-unchanged-imports dir cs is' >>= finish
             where finish : ((𝔹 × include-state) ⊎ string) → IO ((𝔹 × include-state) ⊎ string)
                   finish (inj₁ (b , (mk-include-state asts seen unchanged))) = 
                     return (inj₁ (b && (stringset-contains unchanged (combineFileNames dir file)) ,
                                   mk-include-state asts seen unchanged))
                   finish (inj₂ m) = return (inj₂ m)
        cont (inj₂ m) = return (inj₂ m)
compute-unchanged-imports dir (CmdsNext _ cs) is = compute-unchanged-imports dir cs is
compute-unchanged-imports dir (CmdsStart (Import _ x _)) is with add-cedille-extension x 
compute-unchanged-imports dir (CmdsStart (Import _ x _)) is | file = 
  compute-unchanged dir file is >>= finish
  where finish : include-state ⊎ string → IO ((𝔹 × include-state) ⊎ string)
        finish (inj₁ is') with is' 
        finish (inj₁ is') | (mk-include-state asts seen unchanged) = 
          return (inj₁ (stringset-contains unchanged (combineFileNames dir file) , is'))
        finish (inj₂ m) = return (inj₂ m)
compute-unchanged-imports dir (CmdsStart _) is = return (inj₁ (tt , is))

compute-unchanged dir file (mk-include-state asts seen unchanged) with combineFileNames dir file 
compute-unchanged dir file (mk-include-state asts seen unchanged) | input-filename with stringset-insert seen input-filename
compute-unchanged dir file (mk-include-state asts seen unchanged) | input-filename | seen' = 
  if stringset-contains seen input-filename then
     return (inj₁ (mk-include-state asts seen unchanged))
  else
    (doesFileExist input-filename >>= λ b → 
      if b then
        readFiniteFile input-filename >>= processText
      else return (inj₂ ("Could not open the file " ^ input-filename ^ " for reading.")))
  where processText : string → IO (include-state ⊎ string)
        processText x with runRtn (string-to-𝕃char x)
        processText x | inj₁ cs = return (inj₂ ("Parse error in file " ^ input-filename ^ ". "
                                              ^ "Characters left before failure : " ^ (𝕃char-to-string cs)))
        processText x | inj₂ r with rewriteRun r
        processText x | inj₂ r | ParseTree (parsed-start s) :: [] with s 
        processText x | inj₂ r | ParseTree (parsed-start s) :: [] | File _ cs _ = 
          compute-unchanged-imports dir cs (mk-include-state (trie-insert asts input-filename s) seen' unchanged) >>= finish
          where finish : (𝔹 × include-state) ⊎ string → IO (include-state ⊎ string)
                finish (inj₁ (imports-are-unchanged , mk-include-state asts seen' unchanged)) = 
                  ced-file-up-to-date dir file >>= λ up-to-date → 
                    let do-add = imports-are-unchanged && up-to-date in 
                     return (inj₁ (mk-include-state asts seen' 
                                    (if do-add 
                                     then (stringset-insert unchanged input-filename)
                                     else unchanged)))
                finish (inj₂ m) = return (inj₂ m) 

        processText x | inj₂ r | _ = return (inj₂ ("Parse error in file " ^ input-filename ^ "."))

-- first compute the set of dependencies which are unchanged, and then process the file
checkFile : (dir : string) → (file : string) → IO toplevel-state
checkFile dir file = 
 compute-unchanged dir file (new-include-state empty-trie empty-stringset) >>= cont1
 where cont1 : include-state ⊎ string → IO toplevel-state
       cont1 (inj₁ (mk-include-state asts _ unchanged)) = 
         writeFile "dbg" ((trie-to-string "\n" (λ _ → "") asts) ^ "\n") >>
         processFile dir file (new-toplevel-state (combineFileNames dir file) asts unchanged) >>= cont
         where cont : 𝔹 × toplevel-state → IO toplevel-state
               cont (_ , s') = return s'
       cont1 (inj₂ m) = return (new-toplevel-global-error (combineFileNames dir file) m)

{-# NO_TERMINATION_CHECK #-}
processArgs : 𝕃 string → IO ⊤ 
processArgs (input-filename :: []) = 
  checkFile (takeDirectory input-filename) (takeFileName input-filename) >>= finish
  where finish : toplevel-state → IO ⊤
        finish (mk-toplevel-state i Γ ss) = 
          if global-error-p ss then putStr (spans-to-string ss) else return triv
processArgs [] =
  getLine >>= cont

  where cont : string → IO ⊤
        cont input-filename with takeDirectory input-filename | takeFileName input-filename
        cont input-filename | dir | file with base-filename file
        cont input-filename | dir | file | base = 
          checkFile dir file >>= finish
          where finish : toplevel-state → IO ⊤
                finish (mk-toplevel-state i Γ ss) = 
                   (if global-error-p ss then putStr (spans-to-string ss)
                   else
                     let e = cede-filename dir base in
                        doesFileExist e >>= λ b → 
                        if b then
                         ((readFiniteFile e) >>= λ s → putStr s)
                        else
                          putStr (global-error-string ("Could not open " ^ e ^ " for reading.")))
                   >> processArgs [] 
processArgs xs = putStr ("Run with the name of one file to process, or run with no command-line arguments and enter the\n"
                       ^ "names of files one at a time followed by newlines (this is for the emacs mode).\n")

main : IO ⊤
main = getArgs >>= processArgs 

