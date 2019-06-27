{

module CedilleOptionsLexer where

import Control.Monad
import Data.Text(Text,pack,unpack)
-- import System.Environment

}

%wrapper "monadUserState"

$alpha   = [a-zA-Z]
$anychar = [ \t\%\(\)\:\.\[\]\,\!\{\}\-=\+\<>\/_]
$numone  = 0-9
$squote  = \"
$homechar = \~

@num      = $numone+
@numpunct = $numone | \' | \-
@anychar  = $alpha | @numpunct | $anychar
@homechar = $homechar?
@path     = $squote @homechar @anychar* $squote

token :-
      <0> import\-directories           { mkTokenEmpty TImpDirs       }
      <0> use\-cede\-files              { mkTokenEmpty TUseCedFiles   }
      <0> make\-rkt\-files              { mkTokenEmpty TMkRktFiles    }
      <0> generate\-logs                { mkTokenEmpty TGenLogs       }
      <0> show\-qualified\-vars         { mkTokenEmpty TShowQualVars  }
      <0> erase\-types                  { mkTokenEmpty TEraseTypes    }
      <0> datatype\-encoding            { mkTokenEmpty TDataEnc       }
      <0> pretty\-print\-columns        { mkTokenEmpty TPrintColumns  }
      <0> true                          { mkTokenEmpty TBoolTrue      }
      <0> false                         { mkTokenEmpty TBoolFalse     }
--      <0> Mendler\-old                  { mkTokenEmpty TEncMendlerOld }
--      <0> Mendler                       { mkTokenEmpty TEncMendler    }
      <0> @path  	                { mkTokenPath  TPath          }
      <0> =	                        { mkTokenEmpty TEq            }
      <0> @num                          { mkTokenNum TNum             }
      <0> \.	                        { mkTokenEmpty TPoint         }      
      <0> $white+		        { skip                        }
      <0> \-\- 				{ begin comment               }
      <comment> . 			{ skip                        }
      <comment> \n			{ begin 0                     }      
      <0> \{\- 				{ begin commentMultiLines     }
      <commentMultiLines> . | \n	{ skip                        }      
      <commentMultiLines> \-\}		{ begin 0                     }

{

data Paths = PathsCons Text Paths
           | PathsNil 
  deriving (Show)

--data DataEnc = Mendler | MendlerOld
--  deriving (Show)

data Opt = GenerateLogs         Bool
           | Lib Paths
           | MakeRktFiles       Bool
           | ShowQualifiedVars  Bool
           | UseCedeFiles       Bool
           | EraseTypes         Bool
           | PrintColumns       Text
           | DatatypeEncoding   (Maybe Text)
  deriving (Show)
  
data Opts = OptsCons Opt Opts
          | OptsNil 
  deriving (Show)

data Start = File Opts
  deriving (Show)

mkTokenEmpty :: TokenClass -> AlexAction Token
mkTokenEmpty c (p, _, _, _) len = return $ Token p c

mkTokenPath :: (Text -> TokenClass) -> AlexAction Token
mkTokenPath c (p, _, _, input) len = return $ Token p (c (pack (take (len-2) (tail input)))) -- remove quotes from the string

mkTokenNum :: (Text -> TokenClass) -> AlexAction Token
mkTokenNum c (p, _, _, input) len = return $ Token p (c (pack (take len input)))

data Token = Token AlexPosn TokenClass
  deriving (Show, Eq)

data TokenClass =
        TBoolTrue
     |  TBoolFalse
     |  TPath Text
     |  TNum Text
     |  TImpDirs
     |  TUseCedFiles
     |  TMkRktFiles
     |  TGenLogs
     |  TShowQualVars
     |  TEraseTypes
     |  TPrintColumns
     |  TDataEnc
--     |  TEncMendler
--     |  TEncMendlerOld
     |  TEq
     |  TPoint
     |  TEOF
  deriving (Show,Eq)

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

{- For testing -}
-- main :: IO ()
-- main = do
--   [ file ] <- getArgs
--   cnt      <- readFile file
--   case (scanner cnt) of
--     Left msg -> putStrLn msg
--     Right tokns -> mapM_ (putStrLn . show) tokns


}
