{

module CedilleParser where

import CedilleTypes
import CedilleLexer hiding (main)

import Data.Text(Text,pack,unpack,append,breakOnEnd)

import Control.Monad
import System.Environment
--import System.Directory

}

%name      cedilleParser Start
%name      types         Type
%name      term          Term
%name      maybetype     MaybeCheckType
%name      deftermtype   DefTermOrType
%name      cmd           Cmd
%name      liftingtype   LiftingType

%tokentype { Token }
%error     { parseError }
%monad     { Alex }
%lexer     { lexer } { Token _ TEOF }

%token
  var        { Token _ (TVar _)    }
  qvar       { Token _ (TQvar _)   }
  kvar       { Token _ (TKvar _)   }
  qkvar      { Token _ (TQKvar _)  }
  fpth       { Token _ (TFpth _)   }
  '.num'     { Token _ (TProj _)   }
  'Π↑'       { Token $$ TPiLift    }
  '➔↑'      { Token $$ TArrowLift }  
  'ε'        { Token $$ TEps       }
  'ε-'       { Token $$ TEpsM      }
  'εl'       { Token $$ TEpsL      }
  'εl-'      { Token $$ TEpsLM     }
  'εr'       { Token $$ TEpsR      }
  'εr-'      { Token $$ TEpsRM     }    
  'import'   { Token $$ TImport    }
  'module'   { Token $$ TModule    }
  'as'       { Token $$ TAs        }
  '{^'       { Token $$ TLSpan     }
  '^}'       { Token $$ TRSpan     }
  'θ'        { Token $$ TTheta     }
  'θ+'       { Token $$ TThetaEq   }
  'θ<'       { Token $$ TThetaVars }
  'ρ'        { Token $$ TRhoPlain  }
  'ρ+'       { Token $$ TRhoPlus   }
  '='        { Token $$ (TSym "=") }  
  '>'        { Token $$ (TSym ">") }
  '_'        { Token _  (TSym "_") }
  '.'        { Token $$ (TSym ".") }
  '('        { Token $$ (TSym "(") }
  ')'        { Token $$ (TSym ")") }
  '['        { Token $$ (TSym "[") }
  ']'        { Token $$ (TSym "]") }
  ','        { Token $$ (TSym ",") }  
  '{'        { Token $$ (TSym "{") }
  '}'        { Token $$ (TSym "}") }
  ':'        { Token $$ (TSym ":") }
  'Π'        { Token $$ (TSym "Π") }
  '∀'        { Token $$ (TSym "∀") }
  'λ'        { Token $$ (TSym "λ") }
  'Λ'        { Token $$ (TSym "Λ") }  
  'ι'        { Token $$ (TSym "ι") }
  '↑'        { Token $$ (TSym "↑") }
  'β'        { Token $$ (TSym "β") }
  '·'        { Token $$ (TSym "·") }
  '-'        { Token $$ (TSym "-") }
  'ς'        { Token $$ (TSym "ς") }
  'χ'        { Token $$ (TSym "χ") }
  'φ'        { Token $$ (TSym "φ") }
  '➾'       { Token $$ (TSym "➾") }
  '➔'       { Token $$ (TSym "➔") }
  '≃'        { Token $$ (TSym "≃") }
  '◂'         { Token $$ (TSym "◂") }
  '●'        { Token $$ (TSym "●") }
  '☆'        { Token $$ (TSym "☆") }
  '★'        { Token $$ (TSym "★") }  
  
%%
  
Start :: { Start }
      : Imports 'module' Qvar Params '.' Cmds LineNo { File (pack "1") $1 (tTxt $3) $4 $6 $7 }  

Imprt :: { Imprt }
      : 'import' Fpth OptAs Args '.'    { Import (pos2Txt $1) (tTxt $2) $3 $4 (pos2Txt1 $5) }

OptAs :: { OptAs }
      :                                 { NoOptAs             }
      | 'as' var                        { SomeOptAs (tTxt $2) }
      
Imports :: { Imports }
        :                               { ImportsStart      }
        | Imprt Imports                 { ImportsNext $1 $2 }
{- Note: Happy is more efficient with left recursive rules, only important for long lists -}

Cmds :: { Cmds }
     :                                  { CmdsStart      }
     | Cmd Cmds                         { CmdsNext $1 $2 }

Cmd :: { Cmd }
    : Imprt                             { ImportCmd $1                                       }
    | DefTermOrType        '.'          { DefTermOrType $1 (pos2Txt1 $2)                     }
    | kvar Params '=' Kind '.'          { DefKind (tPosTxt $1) (tTxt $1) $2 $4 (pos2Txt1 $5) }

MaybeCheckType :: { MaybeCheckType }
               :                        { NoCheckType }
               | '◂' Type               { Type $2     }

Params :: { Params }
       :                                { ParamsNil        }
       | Decl Params                    { ParamsCons $1 $2 }

DefTermOrType :: { DefTermOrType }
              : var MaybeCheckType '=' Term  { DefTerm (tPosTxt $1) (tTxt $1) $2 $4 }
              | var '◂' Kind       '=' Type  { DefType (tPosTxt $1) (tTxt $1) $3 $5 } 

Decl :: { Decl }
     : '(' Bvar ':' Tk ')'              { Decl (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 (pos2Txt1 $5) }

Theta :: { (Theta, PosInfo) }
      : 'θ'                             { (Abstract       , pos2Txt $1) }
      | 'θ+'                            { (AbstractEq     , pos2Txt $1) }
      | 'θ<' Vars '>'                   { (AbstractVars $2, pos2Txt $1) }

Vars :: { Vars }
     : var                              { VarsStart (tTxt $1)    }
     | var Vars                         { VarsNext  (tTxt $1) $2 }

Rho :: { (Rho, PosInfo) }
    : 'ρ'                               { (RhoPlain, pos2Txt $1)  }
    | 'ρ+'                              { (RhoPlus , pos2Txt $1)  }

OptTerm :: { OptTerm }
        :                               { NoTerm                    }
        | '{' Term '}'                  { SomeTerm $2 (pos2Txt1 $3) }

Term :: { Term }
     : Lam Bvar OptClass '.' Term       { Lam (snd $1) (fst $1) (tPosTxt $2) (tTxt $2) $3 $5 }
     | '[' DefTermOrType ']' '-' Term   { Let (pos2Txt $1) $2 $5                             }
     | Theta Lterm Lterms               { Theta (snd $1) (fst $1) $2 $3                      }
     | Aterm                            { $1                                                 }

Aterm :: { Term }
      : Aterm     Lterm                 { App $1 NotErased $2           }
      | Aterm '-' Lterm                 { App $1 Erased    $3           }      
      | Aterm '·' Atype                 { AppTp $1 $3                   } 
      | Lterm                           { $1                            }

Lterm :: { Term }
      : 'β'   OptTerm                   { Beta    (pos2Txt $1) $2                             }
      | 'ε'   Lterm                     { Epsilon (pos2Txt $1) Both               EpsHnf  $2  }
      | 'ε-'  Lterm                     { Epsilon (pos2Txt $1) Both               EpsHanf $2  }
      | 'εl'  Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Left  EpsHnf  $2  }
      | 'εl-' Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Left  EpsHanf $2  }
      | 'εr'  Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Right EpsHnf  $2  }
      | 'εr-' Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Right EpsHanf $2  }
      | 'ς' Lterm                       { Sigma (pos2Txt $1) $2                               }
      | Rho Lterm      '-' Lterm        { Rho (snd $1) (fst $1) $2 $4                         }
      | 'φ' Lterm      '-' Lterm '{' Term '}' { Phi (pos2Txt $1) $2 $4 $6 (pos2Txt1 $7)       }
      | 'χ' MaybeAtype '-' Lterm        { Chi (pos2Txt $1) $2 $4                              }
      | Pterm                           { $1                                                  }

Pterm :: { Term }
      : Qvar                            { Var (tPosTxt $1) (tTxt $1)                  }
      | '(' Term ')'                    { Parens (pos2Txt $1) $2 (pos2Txt1 $3)        } 
      | Pterm '.num'                    { IotaProj $1 (tTxt $2) (tPosTxt2 $2)         } -- shift-reduce conflict with the point of end of command (solution: creates a token '.num')
      | '[' Term ',' Term ']'           { IotaPair (pos2Txt $1) $2 $4 (pos2Txt1 $5)}
      | '●'                             { Hole (pos2Txt $1)                           }      

MaybeAtype :: { MaybeAtype }
           : Atype                      { Atype $1 }
           |                            { NoAtype  }
      
Lterms :: { Lterms }
       : LineNo_1                       { LtermsNil  $1              }
       |     Lterm Lterms               { LtermsCons NotErased $1 $2 }
       | '-' Lterm Lterms               { LtermsCons Erased    $2 $3 }       

OptClass :: { OptClass }
         :                              { NoClass      }
         | ':' Tk                       { SomeClass $2 }

OptType :: { OptType }
        :                               { NoType      }
        | ':' Type                      { SomeType $2 }

Lam :: { (Lam , PosInfo) }
    : 'Λ'                               { (ErasedLambda, pos2Txt $1) }
    | 'λ'                               { (KeptLambda  , pos2Txt $1) }

Type :: { Type }
     : 'Π'    Bvar ':' Tk  '.' Type     { Abs (pos2Txt $1) Pi  (tPosTxt $2) (tTxt $2) $4 $6            }
     | '∀'    Bvar ':' Tk  '.' Type     { Abs (pos2Txt $1) All (tPosTxt $2) (tTxt $2) $4 $6            }
     | 'λ'    Bvar ':' Tk  '.' Type     { TpLambda (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6           }
     | 'ι'    Bvar OptType '.' Type     { Iota     (pos2Txt $1) (tPosTxt $2) (tTxt $2) $3 $5           }
     | LType '➾' Type                  { TpArrow $1 ErasedArrow   $3                                  }
     | LType '➔' Type                  { TpArrow $1 UnerasedArrow $3                                  }
     | LType                            { $1                                                           }
     | '{^' Type '^}'                   { NoSpans $2 (pos2Txt $3)                                      }
--   | '{' Term '≃' Term '}'            { TpEq $2 $4                                                   } -- reduce/reduce conflict with variables and holes in types and terms without brackets

LType :: { Type } 
      : '↑' var '.' Term ':' LiftingType  { Lft (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
      | LType   '·' Atype                 { TpApp $1 $3                                   }
      | LType Lterm                       { TpAppt $1 $2                                  }
      | Atype                             { $1                                            }

Atype :: { Type }
      : '(' Type ')'                    { TpParens (pos2Txt $1) $2 (pos2Txt1 $3) }
      | Qvar                            { TpVar (tPosTxt $1) (tTxt $1)           }
      | '●'                             { TpHole (pos2Txt $1)                    }
      | '{' Term '≃' Term '}'           { TpEq $2 $4                             } -- is it not even better here? not require parenthesis in arrow types! neither in type application (cdot), but we should add info position at the end !

Arg :: { Arg }
    : Lterm                             { TermArg $1 }
    | '·' Atype                         { TypeArg $2 }

Args :: { Args }
     : LineNo_1                         { ArgsNil $1     }
     | Arg Args                         { ArgsCons $1 $2 } 

Kind :: { Kind }
     : 'Π' Bvar ':' Tk '.' Kind         { KndPi (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
     | LKind '➔' Kind                  { KndArrow   $1 $3                                }
     | LType '➔' Kind                  { KndTpArrow $1 $3                                }
     | LKind                            { $1                                              }

LKind :: { Kind }
     : '★'                             { Star (pos2Txt $1)                            }
     | '(' Kind ')'                     { KndParens  (pos2Txt $1) $2 (pos2Txt1 $3)     }
     | qkvar Args                       { KndVar (tPosTxt $1) (tTxt $1) $2             }
     | kvar  Args                       { KndVar (tPosTxt $1) (tTxt $1) $2             }     

LiftingType :: { LiftingType }
            : 'Π↑' Bvar ':' Type '.' LiftingType   { LiftPi (pos2Txt $1) (tTxt $2) $4 $6 } 
            | LliftingType  '➔↑' LiftingType      { LiftArrow   $1 $3                   }
            | Type          '➔↑' LiftingType      { LiftTpArrow $1 $3                   }
            | LliftingType                         { $1                                  }

LliftingType :: { LiftingType }
             : '☆'                                { LiftStar (pos2Txt $1)                    }
             | '(' LiftingType ')'                { LiftParens  (pos2Txt $1) $2 (pos2Txt1 $3)}
             
Tk :: { Tk }
   : Type                               { Tkt $1 }
   | Kind                               { Tkk $1 } 

Bvar :: { Token }
     : '_'                              { $1 }
     | var                              { $1 }

Qvar :: { Token }
     : var                              { $1 }
     | qvar                             { $1 }

Fpth :: { Token }
     : fpth                             { $1 }
     | var                              { $1 }

LineNo :: { PosInfo }
       : {- empty -}                    {% getPos } 

LineNo_1 :: { PosInfo }
         : {- empty -}                  {% getPos_1 } 

{
getPos :: Alex PosInfo
getPos = Alex $ \ s -> return (s , pos2Txt(alex_pos s))

getPos_1 :: Alex PosInfo
getPos_1 = Alex $ \ s -> return (s , pos2Txt_1(alex_pos s))
  
posInfo :: PosInfo
posInfo = pack "0"
  
lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScan >>= f  
  
parseError :: Token -> Alex a
parseError (Token (AlexPn p _ _) t) = alexError $ show (p + 1)

parse :: String -> Either String Start
parse s = runAlex s $ cedilleParser 

parseTxt :: Text -> Either Text Start
parseTxt s = case runAlex (unpack s) $ cedilleParser of
               Prelude.Left  s2 -> Prelude.Left (pack s2)
               Prelude.Right r  -> Prelude.Right r

parseTxt2 :: Text -> Text
parseTxt2 s = case runAlex (unpack s) $ cedilleParser of
               Prelude.Left  s2 -> pack s2
               Prelude.Right r  -> pack $ show r

showStart :: Start -> Text
showStart s = pack (show s)

eqStart :: Start -> Start -> Bool
eqStart = (==)

-- main :: IO ()
-- main = do  
--   s <- getContents
--   case parse s of
--     Prelude.Left  errMsg -> putStrLn $ "Error:"             ++ errMsg
--     Prelude.Right res    -> putStrLn $ "Parser successful, AST:" ++ show res

main :: IO ()
main = do  
  [ file ] <- getArgs
  cnt      <- readFile file
  case parse cnt of
    Prelude.Left  errMsg -> writeFile (file ++ "-result") errMsg
    Prelude.Right res    -> writeFile (file ++ "-result") (show res)

-- processDirectory :: Text -> Text -> (Text -> Text) -> IO ()
-- processDirectory inputDir outputDir transformation = 
--   let outD = unpack outputDir  in
--   let inD  = unpack inputDir   in do
--     files    <- listDirectory inD  >>= filterM (doesFileExist . (++) inD)
--     results  <- mapM (liftM (unpack . transformation . pack) . readFile . (++) inD ) files
--     mapM_ (uncurry writeFile) (zip (map ((++) outD) files) results)

-- main :: IO ()
-- main = processDirectory (pack "test/tests/") (pack "results/result_") parseTxt2

processFile :: Text -> (Text -> Text) -> Text -> IO ()
processFile outputDir transformation filePath =
  let outD  = unpack outputDir  in
  let fileP = unpack filePath   in
  let fileN = unpack $ snd $ breakOnEnd (pack "/") filePath in do
    result <- readFile fileP
    writeFile (outD ++ fileN) (unpack $ transformation $ pack result)


}
