import cedille-options

module communication-util (options : cedille-options.options) where

open import general-util
open import toplevel-state options {IO}

logRopeh : filepath → rope → IO ⊤
logRopeh logFilePath r with cedille-options.options.generate-logs options
...| ff = return triv
...| tt = getCurrentTime >>= λ time →
          withFile logFilePath AppendMode λ hdl →
            hPutRope hdl ([[ "([" ^ utcToString time ^ "] " ]] ⊹⊹ r ⊹⊹ [[ ")\n" ]])
logRope : toplevel-state → rope → IO ⊤
logRope s = logRopeh (toplevel-state.logFilePath s)

logMsg : toplevel-state → (message : string) → IO ⊤
logMsg s msg = logRope s [[ msg ]]

logMsg' : filepath → (message : string) → IO ⊤
logMsg' logFilePath msg = logRopeh logFilePath [[ msg ]]

sendProgressUpdate : string → IO ⊤
sendProgressUpdate msg = putStr "progress: " >> putStr msg >> putStr "\n"

progressUpdate : (filename : string) → {-(do-check : 𝔹) → -} IO ⊤
progressUpdate filename {-do-check-} =
  sendProgressUpdate ((if {-do-check-} tt then "Checking " else "Skipping ") ^ filename)

