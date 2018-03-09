module cedille-options where
open import lib
open import general-util

record options : Set where
  field include-path : stringset
        use-cede-files : 𝔹
        make-rkt-files : 𝔹
        generate-logs : 𝔹
        show-qualified-vars : 𝔹

default-options : options
default-options = record {
  include-path = empty-stringset;
  use-cede-files = tt;
  make-rkt-files = ff;
  generate-logs = ff;
  show-qualified-vars = ff}

str-bool-to-𝔹 : string → 𝔹
str-bool-to-𝔹 "true" = tt
str-bool-to-𝔹 _ = ff

options-to-rope : options → rope
options-to-rope ops =
  [[ "import-directories = " ]] ⊹⊹ [[ 𝕃-to-string (λ fp → "\"" ^ fp ^ "\"") " "
     (stringset-strings (options.include-path ops)) ]] ⊹⊹ end ⊹⊹
  [[ "use-cede-files = " ]] ⊹⊹ [[ 𝔹-s options.use-cede-files ]] ⊹⊹ end ⊹⊹
  [[ "make-rkt-files = " ]] ⊹⊹ [[ 𝔹-s options.make-rkt-files ]] ⊹⊹ end ⊹⊹
  [[ "generate-logs = " ]] ⊹⊹ [[ 𝔹-s options.generate-logs ]] ⊹⊹ end ⊹⊹
  [[ "show-qualified-vars = " ]] ⊹⊹ [[ 𝔹-s options.show-qualified-vars ]] ⊹⊹ end
  where end = [[ ".\n" ]]
        𝔹-s : (options → 𝔹) → string
        𝔹-s f = if f ops then "true" else "false"
