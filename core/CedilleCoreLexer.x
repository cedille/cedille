{

module CedilleCoreLexer where

import Control.Monad

}

%wrapper "monadUserState"

$alpha		= [a-zA-Z]
$numone		= 0-9
$numproj        = 1-2
$numpunct	= [$numone\-\~\#\']
$symbols        = [\.\,\(\)\{\}\[\]\:\-\_·≃★◂=@Ππ∀λιβρδΛςφ]

@proj           = \. $numproj
@var            = $alpha ($alpha | $numpunct)*

token :-
      <0> @proj                                 { mkTokenProj  TProj         }
      <0> $symbols                              { mkToken      TSym          }
      <0> $white+				{ skip'                      }
      <0> @var                                  { mkToken TVar               }
{

errorClosingParenth :: AlexAction Token
errorClosingParenth ((AlexPn p _ _), _, _, _) len = alexError $ "L" ++ show (p + 1)

mkToken :: (String -> TokenClass) -> AlexAction Token
mkToken c (p, _, _, input) len = return $ Token p (c (take len input))

mkTokenProj :: (String -> TokenClass) -> AlexAction Token 
mkTokenProj c (p, _, _, input) len = return $ Token p (c (take (len-1) (tail input)))

data Token = Token AlexPosn TokenClass
  deriving (Show, Eq)

tStr :: Token -> String
tStr (Token _ t) = tcStr t

tcStr :: TokenClass -> String
tcStr (TVar   s)     = s
tcStr (TSym   s)     = s
tcStr (TProj  s)     = s
tcStr TEOF           = ""

data TokenClass =
        TVar   String
     |  TSym   String
     |  TProj  String
     |  TEOF
     deriving Eq

instance Show TokenClass where
  show (TVar   s)    = "TVar "   ++ show s
  show (TSym   s)    = "TSym "   ++ show s
  show (TProj  s)    = "TProj "  ++ show s
  show (TEOF)        = "TEOF"

data AlexUserState = AlexUserState {
      num_open_brackets :: Int
}

alexInitUserState = AlexUserState { num_open_brackets=0 }

alexEOF :: Alex Token
alexEOF = do
  (p, _, _, _) <- alexGetInput
  return $ Token p TEOF

isEOF :: Token -> Bool
isEOF (Token _ TEOF) = True
isEOF _              = False

skip' _input _len = alexMonadScanErrOffset

alexMonadScanErrOffset = do
  inp <- alexGetInput
  sc  <- alexGetStartCode
  case alexScan inp sc of
    AlexEOF -> alexEOF
    AlexError ((AlexPn off _ _),_,_,_) -> alexError $ "L" ++ show (off + 1)
    AlexSkip  inp' len -> do
        alexSetInput inp'
        alexMonadScan
    AlexToken inp' len action -> do
        alexSetInput inp'
        action (ignorePendingBytes inp) len
}
