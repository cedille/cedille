{

module CedilleLexer where

import Control.Monad
import Text.Show.Unicode
import Data.Text(Text,pack)

}

%wrapper "monadUserState"

$alpha		= [a-zA-Zα-ωΑ-Ω]
$numone		= 0-9
$numpunct	= [$numone\-\~\#\_\']  
$symbols        = [\.\,\_\(\)\{\}\[\]\:\-Π∀λ●ι↑➾➔☆β·≃>Λςχφ★◂=]

@num            = $numone+
@proj           = \. @num
@var            = $alpha ($alpha | $numpunct)*
@qvar           = @var (\. @var)+
@kvar           = 𝒌 ($alpha | $numpunct)*
@qkvar          = @kvar (\. @var)+
@fpth           = ($alpha | (\.\.\/)+) ($alpha | $numpunct | \/)*

token :-
      <0> @proj                                 { mkTokenProj  TProj      }
      <0> $symbols                              { mkToken      TSym       }
      <0> Π↑                                    { mkTokenEmpty TPiLift    }
      <0> ➔↑                                   { mkTokenEmpty TArrowLift }      
      <0> ε                                     { mkTokenEmpty TEps       }
      <0> ε\-                                   { mkTokenEmpty TEpsM      }
      <0> εl                                    { mkTokenEmpty TEpsL      }
      <0> εl\-                                  { mkTokenEmpty TEpsLM     }
      <0> εr                                    { mkTokenEmpty TEpsR      }
      <0> εr\-                                  { mkTokenEmpty TEpsRM     }      
      <0> θ                                     { mkTokenEmpty TTheta     }
      <0> θ\+                                   { mkTokenEmpty TThetaEq   }
      <0> θ\<                                   { mkTokenEmpty TThetaVars }
      <0> ρ                                     { mkTokenEmpty TRhoPlain  }
      <0> ρ\+                                   { mkTokenEmpty TRhoPlus   }
      <0> \{\^                                  { mkTokenEmpty TLSpan     }
      <0> \^\}                                  { mkTokenEmpty TRSpan     }
      <0> module                                { mkTokenEmpty TModule    }
      <0> import                                { mkTokenEmpty TImport    }
      <0> as                                    { mkTokenEmpty TAs        }
      <0> $white+				;
      <0> @kvar                                 { mkToken TKvar           }
      <0> @qkvar        			{ mkToken TQKvar          }      
      <0> @var                                  { mkToken TVar            }
      <0> @qvar					{ mkToken TQvar           }
      <0> @fpth				        { mkToken TFpth           }
      <0> \-\- 					{ begin comment           }
      <0> \{\- 					{ begin commentMultiLines }      
      <comment> . 				;
      <comment> \n				{ begin 0                 }
      <commentMultiLines> \-\}			{ begin 0                 }
      <commentMultiLines> . | \n		;      

{

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
tcStr _              = ""

data TokenClass =
        TVar   String
     |  TQvar  String
     |  TFpth  String
     |  TKvar  String
     |  TQKvar String
     |  TSym   String
     |  TProj  String
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
     |  TModule
     |  TTheta
     |  TThetaEq
     |  TThetaVars
     |  TRhoPlain
     |  TRhoPlus
     |  TEOF
     deriving Eq

instance Show TokenClass where
  show (TVar   s)    = "TVar "   ++ ushow s
  show (TQvar  s)    = "TQvar "  ++ ushow s
  show (TFpth  s)    = "TFpth "  ++ ushow s
  show (TKvar  s)    = "TKvar "  ++ ushow s
  show (TQKvar s)    = "TQKvar " ++ ushow s
  show (TSym   s)    = "TSym "   ++ ushow s
  show (TProj  s)    = "TProj "  ++ ushow s
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
  show (TModule)     = "TModule"
  show (TTheta)      = "TTheta"
  show (TThetaEq)    = "TThetaEq"
  show (TThetaVars)  = "TThetaVars"
  show (TRhoPlain)   = "TRhoPlain"
  show (TRhoPlus)    = "TRhoPlus"
  show (TEOF)        = "TEOF"

type AlexUserState = ()
alexInitUserState = ()

alexEOF :: Alex Token
alexEOF = do
  (p, _, _, _) <- alexGetInput
  return $ Token p TEOF

isEOF :: Token -> Bool
isEOF (Token _ TEOF) = True
isEOF _              = False

scanner :: String -> Either String [Token]
scanner str = 
  let loop = do
        tok <- alexMonadScan
        if isEOF tok
          then return []
          else do toks <- loop; return (tok:toks)
  in runAlex str loop

main :: IO ()
main = do
  s <- getContents
  case (scanner s) of
    Left msg -> putStrLn msg
    Right tokns -> mapM_ (putStrLn . show) tokns

}
