module cedille-options where
open import lib
open import general-util
open import options-types public

record options : Set where
  constructor mk-options
  field include-path : 𝕃 string × stringset
        use-cede-files : 𝔹
        make-rkt-files : 𝔹
        generate-logs : 𝔹
        show-qualified-vars : 𝔹
        erase-types : 𝔹
        datatype-encoding : data-encoding
        pretty-print-columns : ℕ

        -- Internal use only
        during-elaboration : 𝔹

default-options : options
default-options = record {
  include-path = [] , empty-stringset;
  use-cede-files = tt;
  make-rkt-files = ff;
  generate-logs = ff;
  show-qualified-vars = ff;
  erase-types = tt;
  datatype-encoding = Mendler;
  pretty-print-columns = 80;
  during-elaboration = ff}

include-path-insert : string → 𝕃 string × stringset → 𝕃 string × stringset
include-path-insert s (l , ss) =
  if stringset-contains ss s
    then l , ss
    else s :: l , stringset-insert ss s

options-to-rope : options → rope
options-to-rope ops =
  comment "Cedille Options File" ⊹⊹ [[ "\n" ]] ⊹⊹
  comment "List of directories to search for imported files in" ⊹⊹
  comment "Each directory should be space-delimited and inside double quotes" ⊹⊹
  comment "The current file's directory is automatically searched first, before import-directories" ⊹⊹
  comment "If a filepath is relative, it is considered relative to this options file" ⊹⊹
  option "import-directories"
    (𝕃-to-string (λ fp → "\"" ^ fp ^ "\"") " " (fst (options.include-path ops))) ⊹⊹
  comment "Cache navigation spans for performance" ⊹⊹
  option "use-cede-files" (𝔹-s options.use-cede-files) ⊹⊹
--  comment "Compile Cedille files to Racket after they are checked"⊹⊹
--  option "make-rkt-files" (𝔹-s options.make-rkt-files) ⊹⊹
  comment "Write logs to ~/.cedille/log" ⊹⊹
  option "generate-logs" (𝔹-s options.generate-logs) ⊹⊹
  comment "Print variables fully qualified" ⊹⊹
  option "show-qualified-vars" (𝔹-s options.show-qualified-vars) ⊹⊹
  comment "Print types erased" ⊹⊹
  option "erase-types" (𝔹-s options.erase-types) ⊹⊹
  comment "Preferred number of columns to pretty print elaborated files with" ⊹⊹
  option "pretty-print-columns" (ℕ-to-string (options.pretty-print-columns ops)) ⊹⊹
  comment "Datatype encoding to use when elaborating to Cedille Core" ⊹⊹
  option "datatype-encoding" (enc-s options.datatype-encoding)
  
  where
  𝔹-s : (options → 𝔹) → string
  𝔹-s f = if f ops then "true" else "false"

  enc-s : (options → data-encoding) → string
  enc-s f with f ops
  ...| Mendler = "Mendler"
  ...| Mendler-old = "Mendler-old"

  comment : string → rope
  comment s = [[ "-- " ]] ⊹⊹ [[ s ]] ⊹⊹ [[ "\n" ]]

  option : (name : string) → (value : string) → rope
  option name value = [[ name ]] ⊹⊹ [[ " = " ]] ⊹⊹ [[ value ]] ⊹⊹ [[ ".\n\n" ]]
