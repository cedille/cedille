{

module CedilleLexer where

import Control.Monad
import Data.Text(Text,pack)

}

%wrapper "monadUserState"

$alpha		= [a-zA-Zα-ωΑ-Ω]
$numone		= 0-9
$numpunct	= [$numone\-\~\#\_\'\!]  
$symbols        = [\.\,\_\(\)\{\}\[\]\:\-\+Π∀λ●ι↑➾➔☆β·≃\<>Λςχφ★◂=@δ]

@num            = $numone+
@proj           = \. @num
@var            = $alpha ($alpha | $numpunct)*
@qvar           = @var (\. @var)+
@kvar           = 𝒌 ($alpha | $numpunct)*
@qkvar          = @kvar (\. @var)+
@fpth           = ($alpha | (\.\.\/)+) ($alpha | $numpunct | \/)*

token :-
      <0> @proj                                 { mkTokenProj  TProj         }
      <0> $symbols                              { mkToken      TSym          }
      <0> @num                                  { mkToken      TNum          }
      <0> Π↑                                    { mkTokenEmpty TPiLift       }
      <0> ➔↑                                    { mkTokenEmpty TArrowLift    }      
      <0> ε                                     { mkTokenEmpty TEps          }
      <0> ε\-                                   { mkTokenEmpty TEpsM         }
      <0> εl                                    { mkTokenEmpty TEpsL         }
      <0> εl\-                                  { mkTokenEmpty TEpsLM        }
      <0> εr                                    { mkTokenEmpty TEpsR         }
      <0> εr\-                                  { mkTokenEmpty TEpsRM        }      
      <0> θ                                     { mkTokenEmpty TTheta        }
      <0> θ\+                                   { mkTokenEmpty TThetaEq      }
      <0> θ\<                                   { mkTokenEmpty TThetaVars    }
      <0> ρ                                     { mkTokenEmpty TRho          }
      <0> \{\^                                  { mkTokenEmpty TLSpan        }
      <0> \^\}                                  { mkTokenEmpty TRSpan        }
      <0> module                                { mkTokenEmpty TModule       }
      <0> import                                { mkTokenEmpty TImport       }
      <0> as                                    { mkTokenEmpty TAs           }
      <0> public                                { mkTokenEmpty TPublic       }
      <0> $white+				{ skip'                      }
      <0> @kvar                                 { mkToken TKvar              }
      <0> @qkvar        			{ mkToken TQKvar             }      
      <0> @var                                  { mkToken TVar               }
      <0> @qvar					{ mkToken TQvar              }
      <0> @fpth				        { mkToken TFpth              }
      <0> \-\- 					{ begin' comment             }
      <0> \-\}                                  { errorClosingParenth        }
      <comment> . 				{ skip'                      }
      <comment> \n				{ begin' 0                   }
      <0> \{\- 					{ mkCommentMultiLines        }          <commentMultiLines> \-\}                  { mkCommentMultiLinesDec     }
      <commentMultiLines> \{\-                  { mkCommentMultiLinesInc     } 
      <commentMultiLines> . | \n		{ skip'                      }   

{

errorClosingParenth :: AlexAction Token
errorClosingParenth ((AlexPn p _ _), _, _, _) len = alexError $ "L" ++ show (p + 1)

mkCommentMultiLines :: AlexAction Token
mkCommentMultiLines _ _ = do
  alexSetStartCode commentMultiLines
  alexSetUserState AlexUserState{ num_open_brackets=0 }
  alexMonadScan

mkCommentMultiLinesInc :: AlexAction Token
mkCommentMultiLinesInc _ _ = do
  s <- alexGetUserState
  alexSetUserState s{num_open_brackets=(num_open_brackets s) + 1}
  alexMonadScan

mkCommentMultiLinesDec :: AlexAction Token
mkCommentMultiLinesDec _ _ = do
  s <- alexGetUserState
  if (num_open_brackets s == 0) then do
    alexSetStartCode 0
    alexMonadScan    
  else do
    alexSetUserState s{num_open_brackets=(num_open_brackets s) - 1}
    alexMonadScan    

mkTokenEmpty :: TokenClass -> AlexAction Token
mkTokenEmpty c (p, _, _, _)     len = return $ Token p c

mkToken :: (String -> TokenClass) -> AlexAction Token
mkToken c (p, _, _, input) len = return $ Token p (c (take len input))

mkTokenProj :: (String -> TokenClass) -> AlexAction Token 
mkTokenProj c (p, _, _, input) len = return $ Token p (c (take (len-1) (tail input)))

data Token = Token AlexPosn TokenClass
  deriving (Show, Eq)

tPos :: Token -> AlexPosn
tPos (Token p _) = p

pos2Txt :: AlexPosn -> Text
pos2Txt (AlexPn p _ _) = pack (show (p+1))

pos2Txt0 :: AlexPosn -> Text
pos2Txt0 (AlexPn p _ _) = pack (show p)

pos2Txt1 :: AlexPosn -> Text
pos2Txt1 (AlexPn p _ _) = pack (show (p+2))

-- used for .num
pos2Txt2 :: AlexPosn -> Text
pos2Txt2 (AlexPn p _ _) = pack (show (p+3))

-- used for ArgsNil
pos2Txt_1 :: AlexPosn -> Text
pos2Txt_1 (AlexPn p _ _) = pack (show (p-1))

tPosTxt :: Token -> Text
tPosTxt (Token p _) = pos2Txt p

tPosTxt2 :: Token -> Text
tPosTxt2 (Token p _) = pos2Txt2 p

posEnd :: Token -> Text
posEnd (Token (AlexPn p a b) c) = pack (show (1 + p + (length (tStr (Token (AlexPn p a b) c)))))

tTxt :: Token -> Text
tTxt (Token _ t) = pack (tcStr t)

tStr :: Token -> String
tStr (Token _ t) = tcStr t

tcStr :: TokenClass -> String
tcStr (TVar   s)     = s
tcStr (TQvar  s)     = s
tcStr (TFpth  s)     = s
tcStr (TKvar  s)     = s
tcStr (TQKvar s)     = s
tcStr (TSym   s)     = s
tcStr (TProj  s)     = s
tcStr (TNum   s)     = s
tcStr _              = ""

data TokenClass =
        TVar   String
     |  TQvar  String
     |  TFpth  String
     |  TKvar  String
     |  TQKvar String
     |  TSym   String
     |  TProj  String
     |  TNum   String
     |  TPiLift
     |  TArrowLift     
     |  TEps
     |  TEpsM
     |  TEpsL
     |  TEpsLM
     |  TEpsR
     |  TEpsRM    
     |  TLSpan     
     |  TRSpan
     |  TImport
     |  TAs
     |  TPublic
     |  TModule
     |  TTheta
     |  TThetaEq
     |  TThetaVars
     |  TRho
     |  TEOF
     deriving Eq

instance Show TokenClass where
  show (TVar   s)    = "TVar "   ++ show s
  show (TQvar  s)    = "TQvar "  ++ show s
  show (TFpth  s)    = "TFpth "  ++ show s
  show (TKvar  s)    = "TKvar "  ++ show s
  show (TQKvar s)    = "TQKvar " ++ show s
  show (TSym   s)    = "TSym "   ++ show s
  show (TProj  s)    = "TProj "  ++ show s
  show (TNum   s)    = "TNum "   ++ show s
  show (TPiLift)     = "TPiLift"
  show (TArrowLift)  = "TArrowLift"    
  show (TEps)        = "TEps"
  show (TEpsM)       = "TEpsM"
  show (TEpsL)       = "TEpsL"
  show (TEpsLM)      = "TEpsLM"
  show (TEpsR)       = "TEpsR"
  show (TEpsRM)      = "TEpsRM"    
  show (TLSpan)      = "TLSpan"
  show (TRSpan)      = "TRSpan"
  show (TImport)     = "TImport"
  show (TAs)         = "TAs"
  show (TPublic)     = "TPublic"
  show (TModule)     = "TModule"
  show (TTheta)      = "TTheta"
  show (TThetaEq)    = "TThetaEq"
  show (TThetaVars)  = "TThetaVars"
  show (TRho)        = "TRho"
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

-- ignore this token, but set the start code to a new value
-- begin :: Int -> AlexAction result
begin' code _input _len = do alexSetStartCode code; alexMonadScanErrOffset

-- andBegin' :: AlexAction result -> Int -> AlexAction result
-- andBegin' act code _input _len = do act _input _len; alexSetStartCode code; alexMonadScanErrOffset

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

-- scanner :: String -> Either String [Token]
-- scanner str = 
--   let loop = do
--         tok <- alexMonadScan
--         if isEOF tok
--           then return []
--           else do toks <- loop; return (tok:toks)
--   in runAlex str loop

-- main :: IO ()
-- main = do
--   s <- getContents
--   case (scanner s) of
--     Left msg -> putStrLn msg
--     Right tokns -> mapM_ (putStrLn . show) tokns

}
