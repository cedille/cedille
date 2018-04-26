{

module CedilleCoreParser where

import CedilleCoreTypes
import CedilleCoreToString
import CedilleCoreLexer hiding (main)

import Control.Monad
import System.Environment

}

%name      cedilleCoreParser Cmds
%name      cmd           Cmd
%name      types         Type
%name      term          Term
%name      kind          Kind

%tokentype { Token }
%error     { parseError }
%monad     { Alex }
%lexer     { lexer } { Token _ TEOF }

%token
  var        { Token _  (TVar _)   }
  '.num'     { Token _  (TProj _)  }
  '_'        { Token _  (TSym "_") }
  '='        { Token $$ (TSym "=") }
  '◂'        { Token $$ (TSym "◂") }
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
  'π'        { Token $$ (TSym "π") }
  '∀'        { Token $$ (TSym "∀") }
  'λ'        { Token $$ (TSym "λ") }
  'Λ'        { Token $$ (TSym "Λ") }  
  'ι'        { Token $$ (TSym "ι") }
  'β'        { Token $$ (TSym "β") }
  'δ'        { Token $$ (TSym "δ") }
  '·'        { Token $$ (TSym "·") }
  '-'        { Token $$ (TSym "-") }
  'ς'        { Token $$ (TSym "ς") }
  'ρ'        { Token $$ (TSym "ρ") }
  'φ'        { Token $$ (TSym "φ") }
  '≃'        { Token $$ (TSym "≃") }
  '★'        { Token $$ (TSym "★") }  
  '@'        { Token $$ (TSym "@") }
  
%%

Cmds :: { Cmds }
     :                                 { CmdsStart      }
     | Cmd Cmds                        { CmdsNext $1 $2 }

Cmd :: { Cmd }
    : var '=' Term '.' { TermCmd (tStr $1) $3 }
    | var '◂' '=' Type '.' { TypeCmd (tStr $1) $4 } 

Term :: { Term }
     : 'λ' Bvar ':' Type '.' Term { TmLambda (tStr $2) $4 $6 }
     | 'Λ' Bvar ':' Tk '.' Term { TmLambdaE (tStr $2) $4 $6 }
     | 'ρ' LTerm '@' var '.' PureType '-' Term { Rho $2 (tStr $4) $6 $8 }
     | 'φ' LTerm '-' Term '{' PureTerm '}' { Phi $2 $4 $6 }
     | 'δ' PureType '-' Term { Delta $2 $4 }
     | ATerm { $1 }

ATerm :: { Term }
      : ATerm VTerm { TmAppTm $1 $2 }
      | ATerm '-' VTerm { TmAppTmE $1 $3 }
      | ATerm '·' VType { TmAppTp $1 $3 }
      | LTerm { $1 }

LTerm :: { Term }
      : 'ς' LTerm { Sigma $2 }
      | VTerm { $1 }

VTerm :: { Term }
      : var { TmVar (tStr $1) }
      | 'β' VPureTerm '{' PureTerm '}' { Beta $2 $4 }
      | '[' Term ',' Term '@' var '.' Type ']' { TmIota $2 $4 (tStr $6) $8 }
      | VTerm '.num' { mkIotaProj $1 (tStr $2) }
      | '(' Term ')' { $2 }

PureTerm :: { PureTerm }
         : 'λ' Bvar '.' PureTerm { PureLambda (tStr $2) $4 }
         | APureTerm { $1 }

APureTerm :: { PureTerm }
          : APureTerm VPureTerm { PureApp $1 $2 }
          | VPureTerm { $1 }

VPureTerm :: { PureTerm }
          : var { PureVar (tStr $1) }
          | '(' PureTerm ')' { $2 }

Type :: { Type }
     : 'λ' Bvar ':' Tk '.' Type { TpLambda (tStr $2) $4 $6 }
     | '∀' Bvar ':' Tk '.' Type { TpAll (tStr $2) $4 $6 }
     | 'Π' Bvar ':' Type '.' Type { TpPi (tStr $2) $4 $6 }
     | 'ι' Bvar ':' Type '.' Type { TpIota (tStr $2) $4 $6 }
     | AType { $1 }

AType :: { Type }
      : AType '·' VType { TpAppTp $1 $3 }
      | AType VTerm { TpAppTm $1 $2 }
      | VType { $1 }

VType :: { Type }
      : var                           { TpVar (tStr $1) }
      | '{' PureTerm '≃' PureTerm '}' { TpEq $2 $4 }
      | '(' Type ')'                  { $2 }

PureType :: { PureType }
     : 'λ' Bvar ':' PureTk '.' PureType   { TpLambda (tStr $2) $4 $6 }
     | '∀' Bvar ':' PureTk '.' PureType   { TpAll (tStr $2) $4 $6 }
     | 'Π' Bvar ':' PureType '.' PureType { TpPi (tStr $2) $4 $6 }
     | 'ι' Bvar ':' PureType '.' PureType { TpIota (tStr $2) $4 $6 }
     | APureType { $1 }

APureType :: { PureType }
      : APureType '·' VPureType  { TpAppTp $1 $3 }
      | APureType VPureTerm      { TpAppTm $1 $2 }
      | VPureType                { $1 }

VPureType :: { PureType }
      : var                           { TpVar (tStr $1) }
      | '{' PureTerm '≃' PureTerm '}' { TpEq $2 $4 }
      | '(' PureType ')'              { $2 }

Kind :: { Kind }
     : 'π' Bvar ':' Tk '.' Kind         { KdPi (tStr $2) $4 $6 }
     | '★'                             { Star }
     | '(' Kind ')'                    { $2 }

PureKind :: { PureKind }
     : 'π' Bvar ':' PureTk '.' PureKind  { KdPi (tStr $2) $4 $6 }
     | '★'                             { Star }
     | '(' PureKind ')'                { $2 }

Tk :: { Tk }
   : Type  { Tkt $1 }
   | Kind { Tkk $1 }

PureTk :: { PureTk }
       : PureType  { Tkt $1 }
       | PureKind { Tkk $1 }

Bvar :: { Token }
     : '_' { $1 }
     | var { $1 }

{
lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScanErrOffset >>= f  

mkIotaProj :: Term -> String -> Term
mkIotaProj tm "1" = IotaProj1 tm
mkIotaProj tm "2" = IotaProj2 tm
mkIotaProj tm _ = TmVar "This should never happen (IotaProj with a number other than 1 or 2"

parseError :: Token -> Alex a
parseError (Token (AlexPn p _ _) t) = alexError $ "P" ++ show (p + 1)

parseStr :: String -> Either (Either String String) Cmds
parseStr s = case runAlex s $ cedilleCoreParser of
               Prelude.Left  s' -> case head s' of {
                                     'L' -> Prelude.Left (Prelude.Left  (tail s'));
                                     'P' -> Prelude.Left (Prelude.Right (tail s'));
                                     _   -> Prelude.Left (Prelude.Right "0") -- This should never happen
                                   }
               Prelude.Right r  -> Prelude.Right r

main :: IO ()
main = do  
  [ file ] <- getArgs
  cnt      <- readFile file
  case parseStr cnt of 
    Prelude.Left  (Prelude.Left  errMsg) -> writeFile (file ++ "-result") errMsg
    Prelude.Left  (Prelude.Right errMsg) -> writeFile (file ++ "-result") errMsg
    Prelude.Right res                    -> writeFile (file ++ "-result") (show res)    
}
