module monad-instances where
open import lib
open import general-util

instance
  IO-monad : monad IO
  IO-monad = record {returnM = return; bindM = _>>=_}

instance
  id-monad : monad id
  id-monad = record {returnM = id; bindM = λ a f → f a}
