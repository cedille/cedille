{

module CedilleParser where

import CedilleTypes
import CedilleLexer hiding (main)

import Data.Text(Text,pack,unpack)
import Control.Monad
import System.Environment

}

%name      cedilleParser Start
%name      types         Type
%name      term          Term
%name      kind          Kind
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
  num        { Token _ (TNum _)    }
  '.num'     { Token _ (TProj _)   }
  'Π↑'       { Token $$ TPiLift    }
  '➔↑'       { Token $$ TArrowLift }  
  'ε'        { Token $$ TEps       }
  'ε-'       { Token $$ TEpsM      }
  'εl'       { Token $$ TEpsL      }
  'εl-'      { Token $$ TEpsLM     }
  'εr'       { Token $$ TEpsR      }
  'εr-'      { Token $$ TEpsRM     }    
  'import'   { Token $$ TImport    }
  'module'   { Token $$ TModule    }
  'as'       { Token $$ TAs        }
  'data'     { Token $$ TData      }    
  'public'   { Token $$ TPublic    }
  'opaque'   { Token $$ TOpaque    }
  'open'     { Token $$ TOpen      }
  '{^'       { Token $$ TLSpan     }
  '^}'       { Token $$ TRSpan     }
  'θ'        { Token $$ TTheta     }
  'θ+'       { Token $$ TThetaEq   }
  'θ<'       { Token $$ TThetaVars }
  'ρ'        { Token $$ TRho       }
  'δ'        { Token $$ (TSym "δ") }
  '='        { Token $$ (TSym "=") }  
  '<'        { Token $$ (TSym "<") }
  '>'        { Token $$ (TSym ">") }
  '+'        { Token $$ (TSym "+") }
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
  '➾'        { Token $$ (TSym "➾") }
  '➔'        { Token $$ (TSym "➔") }
  '≃'        { Token $$ (TSym "≃") }
  '◂'        { Token $$ (TSym "◂") }
  '@'        { Token $$ (TSym "@") }
  '●'        { Token $$ (TSym "●") }
  '☆'        { Token $$ (TSym "☆") }
  '★'        { Token $$ (TSym "★") }
  'μ'        { Token $$ TMu   }
  'μ\''      { Token $$ TMu'  }
  '|'        { Token $$ TPipe      }    
%%
  
Start :: { Start }
      : Imports 'module' Qvar MParams '.' Cmds LineNo { File (pack "1") $1 (pos2Txt $2) (tPosTxt $3) (tTxt $3) $4 $6 $7 }  

Imprt :: { Imprt }
      : 'import' OptPublic Fpth OptAs MArgs '.'    { Import (pos2Txt $1) $2 (tPosTxt $3) (tTxt $3) $4 $5 (pos2Txt1 $6) }

OptAs :: { OptAs }
      :                                 { NoOptAs                          }
      | 'as' var                        { SomeOptAs (tPosTxt $2) (tTxt $2) }

OptPublic :: { OptPublic }
          :                             { NotPublic           }
          | 'public'                    { IsPublic            }
      
Imports :: { Imports }
        :                               { ImportsStart      }
        | Imprt Imports                 { ImportsNext $1 $2 }
{- Note: Happy is more efficient with left recursive rules, only important for long lists -}

Cmds :: { Cmds }
     :                                  { CmdsStart      }
     | Cmd Cmds                         { CmdsNext $1 $2 }

OptOpaque :: { Opacity }
          :          { OpacTrans }
          | 'opaque' { OpacOpaque  }

Cmd :: { Cmd }
    : Imprt                             { ImportCmd $1                                       }
    | OptOpaque DefTermOrType '.'       { DefTermOrType $1 $2 (pos2Txt1 $3)                  }
    | DefDatatype             '.'       { DefDatatype   $1 (pos2Txt1 $2)                     }
    | kvar KParams '=' Kind   '.'       { DefKind (tPosTxt $1) (tTxt $1) $2 $4 (pos2Txt1 $5) }

MaybeCheckType :: { OptType }
               :                        { NoType      }
               | '◂' Type               { SomeType $2 }

MParams :: { Params }
       :                                { ParamsNil        }
       | MDecl MParams                  { ParamsCons $1 $2 }

KParams :: { Params }
       :                                { ParamsNil        }
       | KDecl KParams                  { ParamsCons $1 $2 }

DefDatatype :: { DefDatatype }
    : 'data' var MParams ':' Kind '='  OptPipe DataConsts  { Datatype (pos2Txt $1) (tPosTxt $2) (tTxt $2) $3 $5 $8       posInfo } 
    | 'data' var MParams ':' Kind '='                      { Datatype (pos2Txt $1) (tPosTxt $2) (tTxt $2) $3 $5 DataNull posInfo }            

DataConst :: { DataConst }
          : var ':' Type                { DataConst (tPosTxt $1) (tTxt $1) $3 }

DataConsts :: { DataConsts }
           : DataConst                  { DataCons $1  DataNull }           
           | DataConst '|' DataConsts   { DataCons $1  $3       }

DefTermOrType :: { DefTermOrType }
              : var MaybeCheckType '=' Term  { DefTerm (tPosTxt $1) (tTxt $1) $2 $4 }
              | var '◂' Kind       '=' Type  { DefType (tPosTxt $1) (tTxt $1) $3 $5 } 

MDecl :: { Decl }
     : '(' Bvar ':' Tk ')'              { Decl (pos2Txt $1) (tPosTxt $2) NotErased (tTxt $2) $4 (pos2Txt1 $5) }
     | '{' Bvar ':' Type '}'            { Decl (pos2Txt $1) (tPosTxt $2) Erased (tTxt $2) (Tkt $4) (pos2Txt1 $5) }

KDecl :: { Decl }
     : '(' Bvar ':' Tk ')'              { Decl (pos2Txt $1) (tPosTxt $2) NotErased (tTxt $2) $4 (pos2Txt1 $5) }

Lam :: { (MaybeErased , PosInfo) }
    : 'Λ'                               { (Erased,    pos2Txt $1) }
    | 'λ'                               { (NotErased, pos2Txt $1) }

Theta :: { (Theta, PosInfo) }
      : 'θ'                             { (Abstract       , pos2Txt $1) }
      | 'θ+'                            { (AbstractEq     , pos2Txt $1) }
      | 'θ<' Vars '>'                   { (AbstractVars $2, pos2Txt $1) }

Vars :: { Vars }
     : var                              { VarsStart (tTxt $1)    }
     | var Vars                         { VarsNext  (tTxt $1) $2 }

OptPlus :: { OptPlus }
        :     { RhoPlain }
        | '+' { RhoPlus  }

OptNums :: { OptNums }
        :              { NoNums      }
        | '<' Nums '>' { SomeNums $2 }

OptGuide :: { OptGuide }
         :                   { NoGuide }
         | '@' Bvar '.' Type { Guide (tPosTxt $2) (tTxt $2) $4 }

OptType :: { OptType }
           : Atype                      { SomeType $1 }
           |                            { NoType  }

OptClass :: { OptClass }
         :                              { NoClass      }
         | ':' Tk                       { SomeClass $2 }

Nums :: { Nums }
     : Num                              { NumsStart (tTxt $1) }
     | Num Nums                         { NumsNext (tTxt $1) $2 }

OptTerm :: { OptTerm }
        :                               { NoTerm                    }
        | '{' Term '}'                  { SomeTerm $2 (pos2Txt1 $3) }

OptEqTerm :: { OptTerm }
          :                             { NoTerm                    }
          | '<' Term '>'                { SomeTerm $2 (pos2Txt1 $3) }

MArg :: { Arg }
    : Lterm                             { TermArg NotErased $1 }
    | '-' Lterm                         { TermArg Erased $2 }
    | '·' Atype                         { TypeArg $2 }

MArgs :: { Args }
     :                                  { ArgsNil        }
     | MArg MArgs                       { ArgsCons $1 $2 }

KArg :: { Arg }
    : Lterm                             { TermArg NotErased $1 }
    | '·' Atype                         { TypeArg $2 }

KArgs :: { Args }
     :                                  { ArgsNil        }
     | KArg KArgs                       { ArgsCons $1 $2 }

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
     | Qvar                             { $1 }

Num :: { Token }
    : num                               { $1 }

LineNo :: { PosInfo }
       : {- empty -}                    {% getPos } 

LineNo_1 :: { PosInfo }
         : {- empty -}                  {% getPos_1 } 

Term :: { Term }
     : Lam Bvar OptClass '.' Term       { Lam (snd $1) (fst $1) (tPosTxt $2) (tTxt $2) $3 $5 }
     | '[' DefTermOrType ']' '-' Term   { Let (pos2Txt $1) $2 $5                             }
     | 'open' Qvar '-' Term             { Open (pos2Txt $1) (tTxt $2) $4                     }
     | 'ρ' OptPlus OptNums Lterm OptGuide '-' Term { Rho (pos2Txt $1) $2 $3 $4 $5 $7 }
     | 'φ' Lterm '-' Term '{' Term '}'  { Phi (pos2Txt $1) $2 $4 $6 (pos2Txt1 $7) }
     | 'χ' OptType '-' Term             { Chi (pos2Txt $1) $2 $4 }
     | 'δ' OptType '-' Term             { Delta (pos2Txt $1) $2 $4 }
     | 'μ'  Bvar '.' Term Motive '{'  Cases '}' { Mu (pos2Txt $1) (tTxt $2) $4 $5 (pos2Txt1 $6) $7 (pos2Txt1 $8)   }
     | 'μ\''         Term Motive '{'  Cases '}' { Mu' (pos2Txt $1) $2 $3 (pos2Txt1 $4) $5 (pos2Txt1 $6)            }
     | Theta Lterm Lterms               { Theta (snd $1) (fst $1) $2 $3                      }
     | Aterm                            { $1                                                 }

OptPipe :: { PosInfo }
        :          {% getPos      } 
        | '|'      { pos2Txt $1   }         

Cases :: { Cases }
     :                                  { NoCase                      }
     | '|' var  Varargs '➔' Term Cases  { SomeCase (pos2Txt $1) (tTxt $2) $3 $5 $6 }

Varargs :: { Varargs }
     :                                  { NoVarargs                 }
     |     Bvar  Varargs                { NormalVararg (tTxt $1) $2 }
     | '-' Bvar  Varargs                { ErasedVararg (tTxt $2) $3 }
     | '.' Bvar  Varargs                { TypeVararg   (tTxt $2) $3 }
       
Motive :: { OptType }
     :                                  { NoType          }
     | '@' Type                         { SomeType $2     }  

Aterm :: { Term }
      : Aterm     Lterm                 { App $1 NotErased $2           }
      | Aterm '-' Lterm                 { App $1 Erased    $3           }      
      | Aterm '·' Atype                 { AppTp $1 $3                   } 
      | Lterm                           { $1                            }

Lterm :: { Term }
      : 'β' OptEqTerm OptTerm           { Beta    (pos2Txt $1) $2 $3                          }
      | 'ε'   Lterm                     { Epsilon (pos2Txt $1) Both               EpsHnf  $2  }
      | 'ε-'  Lterm                     { Epsilon (pos2Txt $1) Both               EpsHanf $2  }
      | 'εl'  Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Left  EpsHnf  $2  }
      | 'εl-' Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Left  EpsHanf $2  }
      | 'εr'  Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Right EpsHnf  $2  }
      | 'εr-' Lterm                     { Epsilon (pos2Txt $1) CedilleTypes.Right EpsHanf $2  }
      | 'ς' Lterm                       { Sigma (pos2Txt $1) $2                               }
      | Pterm                           { $1                                                  }

Pterm :: { Term }
      : Qvar                            { Var (tPosTxt $1) (tTxt $1)                  }
      | '(' Term ')'                    { Parens (pos2Txt $1) $2 (pos2Txt1 $3)        } 
      | Pterm '.num'                    { IotaProj $1 (tTxt $2) (tPosTxt2 $2)         } -- shift-reduce conflict with the point of end of command (solution: creates a token '.num')
      | '[' Term ',' Term OptGuide ']'  { IotaPair (pos2Txt $1) $2 $4 $5 (pos2Txt1 $6)}
      | '●'                             { Hole (pos2Txt $1)                           }      
      
Lterms :: { Lterms }
       : LineNo_1                       { LtermsNil  $1              }
       |     Lterm Lterms               { LtermsCons NotErased $1 $2 }
       | '-' Lterm Lterms               { LtermsCons Erased    $2 $3 }

Type :: { Type }
     : 'Π'    Bvar ':' Tk  '.' Type     { Abs (pos2Txt $1) NotErased  (tPosTxt $2) (tTxt $2) $4 $6     }
     | '∀'    Bvar ':' Tk  '.' Type     { Abs (pos2Txt $1) Erased (tPosTxt $2) (tTxt $2) $4 $6         }
     | 'λ'    Bvar ':' Tk  '.' Type     { TpLambda (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6           }
     | 'ι'    Bvar ':' Type '.' Type    { Iota     (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6           }
     | LType '➾' Type                   { TpArrow $1 Erased   $3                                       }
     | LType '➔' Type                   { TpArrow $1 NotErased $3                                      }
     | LType                            { $1                                                           }
     | '{^' Type '^}'                   { NoSpans $2 (pos2Txt $3)                                      }
     | '[' DefTermOrType ']' '-' Type   { TpLet (pos2Txt $1) $2 $5                                     }
--   | '{' Term '≃' Term '}'            { TpEq $2 $4                                                   } -- reduce/reduce conflict with variables and holes in types and terms without brackets

LType :: { Type } 
--    : '↑' var '.' Term ':' LiftingType  { Lft (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
      : LType   '·' Atype                 { TpApp $1 $3                                   }
      | LType Lterm                       { TpAppt $1 $2                                  }
      | Atype                             { $1                                            }

Atype :: { Type }
      : '(' Type ')'                    { TpParens (pos2Txt $1) $2 (pos2Txt1 $3) }
      | Qvar                            { TpVar (tPosTxt $1) (tTxt $1)           }
      | '●'                             { TpHole (pos2Txt $1)                    }
      | '{' Term '≃' Term '}'           { TpEq (pos2Txt $1) $2 $4 (pos2Txt1 $5)  } -- is it not even better here? not require parenthesis in arrow types! neither in type application (cdot), but we should add info position at the end !

Kind :: { Kind }
     : 'Π' Bvar ':' Tk '.' Kind         { KndPi (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
     | LKind '➔' Kind                  { KndArrow   $1 $3                                }
     | LType '➔' Kind                  { KndTpArrow $1 $3                                }
     | LKind                            { $1                                              }

LKind :: { Kind }
     : '★'                              { Star (pos2Txt $1)                              }
     | '(' Kind ')'                     { KndParens  (pos2Txt $1) $2 (pos2Txt1 $3)       }
     | qkvar KArgs                      { KndVar (tPosTxt $1) (tTxt $1) $2 }
     | kvar  KArgs                      { KndVar (tPosTxt $1) (tTxt $1) $2 }     

LiftingType :: { LiftingType }
            : 'Π↑' Bvar ':' Type '.' LiftingType   { LiftPi (pos2Txt $1) (tTxt $2) $4 $6 } 
            | LliftingType  '➔↑' LiftingType       { LiftArrow   $1 $3                   }
            | Type          '➔↑' LiftingType       { LiftTpArrow $1 $3                   }
            | LliftingType                         { $1                                  }

LliftingType :: { LiftingType }
             : '☆'                                { LiftStar (pos2Txt $1)                    }
             | '(' LiftingType ')'                { LiftParens  (pos2Txt $1) $2 (pos2Txt1 $3)}

{
getPos :: Alex PosInfo
getPos = Alex $ \ s -> return (s , pos2Txt0(alex_pos s))

getPos_1 :: Alex PosInfo
getPos_1 = Alex $ \ s -> return (s , pos2Txt_1(alex_pos s))
  
posInfo :: PosInfo
posInfo = pack "0"
  
lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScanErrOffset >>= f  
  
parseError :: Token -> Alex a
parseError (Token (AlexPn p _ _) t) = alexError $ "P" ++ show (p + 1)

parseTxt :: Text -> Either (Either Text Text) Start
parseTxt s = case runAlex (unpack s) $ cedilleParser of
               Prelude.Left  s' -> case head s' of {
                                     'L' -> Prelude.Left (Prelude.Left  (pack (tail s')));
                                     'P' -> Prelude.Left (Prelude.Right (pack (tail s')));
                                     _   -> Prelude.Left (Prelude.Right (pack "0")) -- This should never happen
                                   }
               Prelude.Right r  -> Prelude.Right r

parse :: Alex a -> Text -> Either Text a
parse p s = case runAlex (unpack s) $ p of
	 Prelude.Left  s2 -> Prelude.Left (pack (tail s2)) -- tail removes "L" (lexer error) and "P" (parser error) prefixes
         Prelude.Right r  -> Prelude.Right r
		 
parseTerm :: Text -> Either Text Term
parseTerm  = parse term

parseType :: Text -> Either Text Type
parseType = parse types

parseLiftingType :: Text -> Either Text LiftingType
parseLiftingType = parse liftingtype

parseKind :: Text -> Either Text Kind
parseKind = parse kind

parseDefTermOrType :: Text -> Either Text DefTermOrType
parseDefTermOrType = parse deftermtype

main :: IO ()
main = do  
  [ file ] <- getArgs
  cnt      <- readFile file
  case parseTxt (pack cnt) of 
    Prelude.Left  (Prelude.Left  errMsg) -> writeFile (file ++ "-result") (unpack errMsg)
    Prelude.Left  (Prelude.Right errMsg) -> writeFile (file ++ "-result") (unpack errMsg)
    Prelude.Right res                    -> writeFile (file ++ "-result") (show res)    

}
