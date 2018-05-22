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

@num      = $numone+
@numpunct = $numone | \' | \-
@anychar  = $alpha | @numpunct | $anychar
@path     = $squote @anychar* $squote

token :-
      <0> import\-directories           { mkTokenEmpty TImpDirs       }
      <0> use\-cede\-files              { mkTokenEmpty TUseCedFiles   }
      <0> make\-rkt\-files              { mkTokenEmpty TMkRktFiles    }
      <0> generate\-logs                { mkTokenEmpty TGenLogs       }
      <0> show\-qualified\-vars         { mkTokenEmpty TShowQualVars  }
      <0> make\-core\-files             { mkTokenEmpty TMkCoreFiles   }
      <0> true                          { mkTokenEmpty TBoolTrue      }
      <0> false                         { mkTokenEmpty TBoolFalse     }
      <0> @path  	                { mkTokenPath  TPath          }
      <0> =	                        { mkTokenEmpty TEq            }
      <0> \.	                        { mkTokenEmpty TPoint         }      
      <0> $white+		        { skip                        }
      <0> \-\- 				{ begin comment               }
      <comment> . 			{ skip                        }
      <comment> \n			{ begin 0                     }      
      <0> \{\- 				{ begin commentMultiLines     }
      <commentMultiLines> . | \n	{ skip                        }      
      <commentMultiLines> \-\}		{ begin 0                     }

{

data StrBool = StrBoolFalse | StrBoolTrue
  deriving (Show)

data Paths = PathsCons Text Paths
           | PathsNil 
  deriving (Show)

data Opt = GenerateLogs         StrBool
           | Lib Paths
           | MakeCoreFiles      StrBool
           | MakeRktFiles       StrBool
           | ShowQualifiedVars  StrBool
           | UseCedeFiles       StrBool
  deriving (Show)
  
data Opts = OptsCons Opt Opts
          | OptsNil 
  deriving (Show)

data Start = File Opts
  deriving (Show)

mkTokenEmpty :: TokenClass -> AlexAction Token
mkTokenEmpty c (p, _, _, _) len = return $ Token p c

mkTokenPath :: (Text -> TokenClass) -> AlexAction Token
mkTokenPath c (p, _, _, input)  len = return $ Token p (c (pack (take (len-2) (tail input)))) -- remove quotes from the string

data Token = Token AlexPosn TokenClass
  deriving (Show, Eq)

data TokenClass =
        TBoolTrue
     |  TBoolFalse
     |  TPath      Text
     |  TImpDirs
     |  TUseCedFiles
     |  TMkRktFiles
     |  TMkCoreFiles
     |  TGenLogs
     |  TShowQualVars
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
