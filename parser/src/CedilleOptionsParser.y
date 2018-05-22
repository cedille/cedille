{

module CedilleOptionsParser where

import CedilleOptionsLexer hiding (main)

import Data.Text(Text,pack,unpack)
import Control.Monad
-- import System.Environment
  
}

%name      cedilleOptionsParser Start

%tokentype { Token }
%error     { parseError }
%monad     { Alex }
%lexer     { lexer } { Token _ TEOF }

%token
  'true'                 { Token _  TBoolTrue     }
  'false'                { Token _  TBoolFalse    }
  path                   { Token _  (TPath $$)    }
  'import-directories'   { Token _  TImpDirs      }
  'use-cede-files'       { Token _  TUseCedFiles  }
  'make-rkt-files'       { Token _  TMkRktFiles   }
  'generate-logs'        { Token _  TGenLogs      }
  'show-qualified-vars'  { Token _  TShowQualVars }
  'make-core-files'      { Token _  TMkCoreFiles  }
  '.'                    { Token _  TPoint        }
  '='                    { Token _  TEq           }
  
%%
  
Start :: { Start }
      : Opts    { File $1 }  

Opts :: { Opts }
     :          { OptsNil        }
     | Opt Opts { OptsCons $1 $2 }

Bool :: { StrBool }
     : 'false'  { StrBoolFalse }
     | 'true'   { StrBoolTrue }

Opt :: { Opt }
    : 'import-directories'  '=' Paths  '.'  { Lib          $3 }
    | 'use-cede-files'      '=' Bool   '.'  { UseCedeFiles $3 }
    | 'make-rkt-files'      '=' Bool   '.'  { MakeRktFiles $3 }
    | 'generate-logs'       '=' Bool   '.'  { GenerateLogs $3 }
    | 'show-qualified-vars' '=' Bool   '.'  { ShowQualifiedVars $3 }
    | 'make-core-files'     '=' Bool   '.'  { MakeCoreFiles $3 }

Paths :: { Paths }
      :             { PathsNil        }
      | path Paths  { PathsCons $1 $2 }

{
  
lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScan >>= f  
  
parseError :: Token -> Alex a
parseError (Token (AlexPn _ line column) t) = alexError $ "Syntactic error at line " ++ (show line) ++ ", column " ++ (show column)

parseOptions :: Text -> Either Text Start
parseOptions s = case runAlex (unpack s) $ cedilleOptionsParser of
               Prelude.Left  s' -> Prelude.Left (pack s')
               Prelude.Right r  -> Prelude.Right r

{- For testing  -}

-- main :: IO ()
-- main = do  
--   [ file ] <- getArgs
--   cnt      <- readFile file
--   case parseOptions (pack cnt) of 
--     Prelude.Left  errMsg -> putStrLn (unpack errMsg)
--     Prelude.Right res    -> putStrLn (show res)    

}
