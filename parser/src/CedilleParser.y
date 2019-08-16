{

module CedilleParser where

import CedilleTypes
import CedilleLexer hiding (main)

import Data.Text(Text,pack,unpack)
import Control.Monad
import System.Environment

}

%name      cedilleParser File
%name      typee         Type
%name      terme         Term
%name      kinde         Kind
%name      deftermtype   Def
--%name      cmde          Cmd
--%name      liftingtype   LiftingType

%tokentype { Token }
%error     { parseError }
%monad     { Alex }
%lexer     { lexer } { Token _ TEOF }

%token
  var        { Token _ (TVar _) }
  qvar       { Token _ (TQvar _) }
  kvar       { Token _ (TKvar _) }
  qkvar      { Token _ (TQKvar _) }
  fpth       { Token _ (TFpth _) }
  num        { Token _ (TNum _) }
  '.num'     { Token _ (TProj _) }
--  'Π↑'       { Token $$ TPiLift }
--  '➔↑'       { Token $$ TArrowLift }
  'ε'        { Token $$ TEps }
  'ε-'       { Token $$ TEpsM }
  'εl'       { Token $$ TEpsL }
  'εl-'      { Token $$ TEpsLM }
  'εr'       { Token $$ TEpsR }
  'εr-'      { Token $$ TEpsRM }
  'import'   { Token $$ TImport }
  'module'   { Token $$ TModule }
  'as'       { Token $$ TAs }
  'data'     { Token $$ TData }
  'public'   { Token $$ TPublic }
  'opaque'   { Token $$ TOpaque }
  'open'     { Token $$ TOpen }
  'close'    { Token $$ TClose }
  '{^'       { Token $$ TLSpan }
  '^}'       { Token $$ TRSpan }
  'θ'        { Token $$ TTheta }
  'θ+'       { Token $$ TThetaEq }
  'θ<'       { Token $$ TThetaVars }
  'ρ'        { Token $$ TRho }
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
--  '↑'        { Token $$ (TSym "↑") }
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
--  '☆'        { Token $$ (TSym "☆") }
  '★'        { Token $$ (TSym "★") }
  'μ'        { Token $$ TMu }
  'μP'       { Token $$ TMuP }
  '|'        { Token $$ TPipe }
  '&'      { Token $$ TAnd }
%%
  
File :: { File }
      : Imports 'module' Qvar MParams '.' Cmds LineNo { Module $1 (pos2Txt $2) (tPosTxt $3) (tTxt $3) $4 $6 $7 }

Imprt :: { Imprt }
      : 'import' OptPublic Fpth OptAs MArgs '.'    { Import (pos2Txt $1) $2 (tPosTxt $3) (tTxt $3) $4 $5 (pos2Txt1 $6) }

OptAs :: { Maybe ImportAs }
      :                                 { Nothing }
      | 'as' var                        { Just (ImportAs (tPosTxt $2) (tTxt $2)) }

OptPublic :: { OptPublic }
          :                             { False }
          | 'public'                    { True }
      
Imports :: { Imports }
        :                               { [] }
        | Imprt Imports                 { $1 : $2 }
{- Note: Happy is more efficient with left recursive rules, only important for long lists -}

Cmds :: { Cmds }
     :                                  { [] }
     | Cmd Cmds                         { $1 : $2 }

OptOpaque :: { Opacity }
          :          { True }
          | 'opaque' { False }

Cmd :: { Cmd }
    : Imprt                             { CmdImport $1 }
    | OptOpaque Def '.'                 { CmdDef $1 $2 (pos2Txt1 $3) }
    | DefDatatype             '.'       { CmdData $1 (pos2Txt1 $2) }
    | kvar KParams '=' Kind   '.'       { CmdKind (tPosTxt $1) (tTxt $1) $2 $4 (pos2Txt1 $5) }

MaybeCheckType :: { Maybe Type }
               :                        { Nothing }
               | '◂' Type               { Just $2 }
               | ':' Type               { Just $2 }

MParams :: { Params }
       :                                { [] }
       | MDecl MParams                  { $1 : $2 }

KParams :: { Params }
       :                                { [] }
       | KDecl KParams                  { $1 : $2 }

DefDatatype :: { [ DefDatatype ] }
: 'data' OneDatatype OptMutualDefDatatype { (defDatatypeAddStartingPos (pos2Txt $1) $2) : $3 }

OptMutualDefDatatype :: { [ DefDatatype ] }
  : { [] }
| '&' OneDatatype OptMutualDefDatatype { (defDatatypeAddStartingPos (pos2Txt $1) $2) : $3 }

OneDatatype :: { DefDatatypeA }
  : var MParams ':' Kind '=' OptPipe Ctrs { DefDatatypeA (tPosTxt $1) (tTxt $1) $2 $4 $7 }

Ctr :: { Ctr }
    : var ':' Type    { Ctr (tPosTxt $1) (tTxt $1) $3 }

Ctrs :: { Ctrs }
           :                { [] }
           | Ctr '|' Ctrs   { $1 : $3 }
           | Ctr            { $1 : [] }

Def :: { Def }
              : Bvar MaybeCheckType '=' Term  { DefTerm (tPosTxt $1) (tTxt $1) $2 $4 }
              | Bvar '◂' Kind       '=' Type  { DefType (tPosTxt $1) (tTxt $1) $3 $5 }
              | Bvar ':' Kind       '=' Type  { DefType (tPosTxt $1) (tTxt $1) $3 $5 }

MDecl :: { Param }
     : '(' Bvar ':' Kind ')'            { Param (pos2Txt $1) True  (tPosTxt $2) (tTxt $2) (Tkk $4) (pos2Txt1 $5) }
     | '(' Bvar ':' Type ')'            { Param (pos2Txt $1) False (tPosTxt $2) (tTxt $2) (Tkt $4) (pos2Txt1 $5) }
     | '{' Bvar ':' Type '}'            { Param (pos2Txt $1) True  (tPosTxt $2) (tTxt $2) (Tkt $4) (pos2Txt1 $5) }

KDecl :: { Param }
     : '(' Bvar ':' TpKd ')'              { Param (pos2Txt $1) False (tPosTxt $2) (tTxt $2) $4 (pos2Txt1 $5) }

Lam :: { (MaybeErased, PosInfo) }
    : 'Λ'                               { (True,  pos2Txt $1) }
    | 'λ'                               { (False, pos2Txt $1) }

Theta :: { (Theta, PosInfo) }
      : 'θ'                             { (Abstract,        pos2Txt $1) }
      | 'θ+'                            { (AbstractEq,      pos2Txt $1) }
      | 'θ<' Vars '>'                   { (AbstractVars $2, pos2Txt $1) }

Vars :: { [Var] }
     : Qvar                              { [tTxt $1] }
     | Qvar Vars                         { tTxt $1 : $2 }

OptPlus :: { RhoHnf }
        :     { False }
        | '+' { True }

OptNums :: { Maybe [CedilleTypes.Num] }
        :              { Nothing }
        | '<' Nums '>' { Just $2 }

OptGuide :: { Maybe Guide }
         :                   { Nothing }
         | '@' Bvar '.' Type { Just (Guide (tPosTxt $2) (tTxt $2) $4) }

OptType :: { Maybe Type }
           : Atype                      { Just $1 }
           |                            { Nothing }

OptClass :: { Maybe TpKd }
         :                              { Nothing }
         | ':' TpKd                     { Just $2 }

Nums :: { [CedilleTypes.Num] }
     : Num                              { [tTxt $1] }
     | Num Nums                         { tTxt $1 : $2 }

OptTerm :: { Maybe PosTerm }
        :                               { Nothing }
        | '{' Term '}'                  { Just (PosTerm $2 (pos2Txt1 $3)) }

OptTermAngle :: { Maybe PosTerm }
          :                             { Nothing }
          | '<' Term '>'                { Just (PosTerm $2 (pos2Txt1 $3)) }

MaybeTermAngle :: { Maybe Term }
          :                             { Nothing }
          | '<' Term '>'                { Just $2 }

MArg :: { Arg }
    : Lterm                             { TermArg False $1 }
    | '-' Lterm                         { TermArg True $2 }
    | '·' Atype                         { TypeArg $2 }

MArgs :: { Args }
     :                                  { [] }
     | MArg MArgs                       { $1 : $2 }

KArg :: { Arg }
    : Lterm                             { TermArg False $1 }
    | '·' Atype                         { TypeArg $2 }

KArgs :: { Args }
     :                                  { [] }
     | KArg KArgs                       { $1 : $2 }

TpKd :: { TpKd }
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

--LineNo_1 :: { PosInfo }
--         : {- empty -}                  {% getPos_1 }

Term :: { Term }
     : Lam Bvar OptClass '.' Term       { Lam (snd $1) (fst $1) (tPosTxt $2) (tTxt $2) $3 $5 }
     | '[' Def ']' '-' Term   { Let (pos2Txt $1) False $2 $5 }
     | '{' Def '}' '-' Term   { Let (pos2Txt $1) True  $2 $5 }
     | 'open' Qvar '-' Term             { Open (pos2Txt $1) True (tPosTxt $2) (tTxt $2) $4 }
     | 'close' Qvar '-' Term            { Open (pos2Txt $1) False (tPosTxt $2) (tTxt $2) $4 }
     | 'ρ' OptPlus OptNums Lterm OptGuide '-' Term { Rho (pos2Txt $1) $2 $3 $4 $5 $7 }
     | 'φ' Lterm '-' Term '{' Term '}'  { Phi (pos2Txt $1) $2 $4 $6 (pos2Txt1 $7) }
     | 'χ' OptType '-' Term             { Chi (pos2Txt $1) $2 $4 }
     | 'δ' OptType '-' Term             { Delta (pos2Txt $1) $2 $4 }
     | Theta Lterm Lterms               { Theta (snd $1) (fst $1) $2 $3 }
     | Aterm                            { $1 }

OptPipe :: { PosInfo }
        :          {% getPos }
        | '|'      { pos2Txt $1 }

Cases :: { Cases }
     :                                  { [] }
     | '|' Qvar CaseArgs '➔' Term Cases { Case (tPosTxt $2) (tTxt $2) $3 $5 : $6 }

-- Optional first pipe
CasesAux :: { Cases }
  : Qvar CaseArgs '➔' Term Cases { Case (tPosTxt $1) (tTxt $1) $2 $4 : $5 }
  | Cases                        { $1 }

CaseArgs :: { [CaseArg] }
     :                           { [] }
     |     Bvar CaseArgs         { CaseArg CaseArgTm (tPosTxt $1) (tTxt $1) : $2 }
     | '-' Bvar CaseArgs         { CaseArg CaseArgEr (tPosTxt $2) (tTxt $2) : $3 }
     | '·' Bvar CaseArgs         { CaseArg CaseArgTp (tPosTxt $2) (tTxt $2) : $3 }
       
Motive :: { Maybe Type }
     :                                  { Nothing }
     | '@' Type                         { Just $2 }

Aterm :: { Term }
      : Aterm     Lterm                 { App $1 False $2 }
      | Aterm '-' Lterm                 { App $1 True $3 }
      | Aterm '·' Atype                 { AppTp $1 $3 }
      | Lterm                           { $1 }

Lterm :: { Term }
      : 'β' OptTermAngle OptTerm        { Beta (pos2Txt $1) $2 $3 }
      | 'ε'   Lterm                     { Epsilon (pos2Txt $1) Nothing False $2 }
      | 'ε-'  Lterm                     { Epsilon (pos2Txt $1) Nothing True $2 }
      | 'εl'  Lterm                     { Epsilon (pos2Txt $1) (Just False) False $2 }
      | 'εl-' Lterm                     { Epsilon (pos2Txt $1) (Just False) True $2 }
      | 'εr'  Lterm                     { Epsilon (pos2Txt $1) (Just True) False  $2 }
      | 'εr-' Lterm                     { Epsilon (pos2Txt $1) (Just True) True $2 }
      | 'ς' Lterm                       { Sigma (pos2Txt $1) $2 }
      | Pterm                           { $1 }

Pterm :: { Term }
      : Qvar                            { Var (tPosTxt $1) (tTxt $1) }
      | '(' Term ')'                    { Parens (pos2Txt $1) $2 (pos2Txt1 $3) }
      | Pterm '.num'                    { IotaProj $1 (tTxt $2) (tPosTxt2 $2) } -- shift-reduce conflict with the point of end of command (solution: creates a token '.num')
      | '[' Term ',' Term OptGuide ']'  { IotaPair (pos2Txt $1) $2 $4 $5 (pos2Txt1 $6)}
      | 'μ'  Bvar '.' Term MotiveCases MoreMotiveCases { Mu (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 ($5 : $6) }
      | 'μP' MaybeTermAngle Term MotiveCases { MuPrime (pos2Txt $1) $2 $3 $4  }
      | '●'                             { Hole (pos2Txt $1) }
      
MotiveCases :: { MotiveCases }
  : Motive '{' CasesAux '}' 
  { MotiveCases $1 (pos2Txt1 $2) $3 (pos2Txt1 $4)  }

MoreMotiveCases :: { [ MotiveCases ]}
  : { [] }
  | '&' MotiveCases MoreMotiveCases { $2 : $3 }

Lterms :: { [Lterm] }
       :                                { [] }
       |     Lterm Lterms               { Lterm False $1 : $2 }
       | '-' Lterm Lterms               { Lterm True  $2 : $3 }

Type :: { Type }
     : 'Π' Bvar ':' TpKd '.' Type     { TpAbs (pos2Txt $1) False  (tPosTxt $2) (tTxt $2) $4 $6 }
     | '∀' Bvar ':' TpKd '.' Type     { TpAbs (pos2Txt $1) True (tPosTxt $2) (tTxt $2) $4 $6 }
     | 'λ' Bvar ':' TpKd '.' Type     { TpLam (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
     | 'ι' Bvar ':' Type '.' Type    { TpIota (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
     | LType '➾' Type                   { TpArrow $1 True $3 }
     | LType '➔' Type                   { TpArrow $1 False $3 }
     | LType                            { $1 }
     | '{^' Type '^}'                   { TpNoSpans $2 (pos2Txt $3) }
     | '[' Def ']' '-' Type   { TpLet (pos2Txt $1) $2 $5 }

LType :: { Type } 
--    : '↑' Bvar '.' Term ':' LiftingType  { Lft (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
      : LType   '·' Atype                 { TpApp $1 $3 }
      | LType Lterm                       { TpAppt $1 $2 }
      | Atype                             { $1 }

Atype :: { Type }
      : '(' Type ')'                    { TpParens (pos2Txt $1) $2 (pos2Txt1 $3) }
      | Qvar                            { TpVar (tPosTxt $1) (tTxt $1) }
      | '●'                             { TpHole (pos2Txt $1) }
      | '{' Term '≃' Term '}'           { TpEq (pos2Txt $1) $2 $4 (pos2Txt1 $5) }

Kind :: { Kind }
     : 'Π' Bvar ':' TpKd '.' Kind         { KdAbs (pos2Txt $1) (tPosTxt $2) (tTxt $2) $4 $6 }
     | LKind '➔' Kind                  { KdArrow (Tkk $1) $3 }
     | LType '➔' Kind                  { KdArrow (Tkt $1) $3 }
     | LKind                            { $1 }

LKind :: { Kind }
     : '★'                              { KdStar (pos2Txt $1) }
     | '(' Kind ')'                     { KdParens  (pos2Txt $1) $2 (pos2Txt1 $3) }
     | qkvar KArgs                      { KdVar (tPosTxt $1) (tTxt $1) $2 }
     | kvar  KArgs                      { KdVar (tPosTxt $1) (tTxt $1) $2 }

--LiftingType :: { LiftingType }
--            : 'Π↑' Bvar ':' Type '.' LiftingType   { LiftPi (pos2Txt $1) (tTxt $2) $4 $6 } 
--            | LliftingType  '➔↑' LiftingType       { LiftArrow   $1 $3 }
--            | Type          '➔↑' LiftingType       { LiftTpArrow $1 $3 }
--            | LliftingType                         { $1 }

--LliftingType :: { LiftingType }
--             : '☆'                                { LiftStar (pos2Txt $1) }
--             | '(' LiftingType ')'                { LiftParens  (pos2Txt $1) $2 (pos2Txt1 $3)}

{
defDatatypeAddStartingPos :: Text -> DefDatatypeA -> DefDatatype
defDatatypeAddStartingPos p (DefDatatypeA p' v ps k cs) = DefDatatype p p' v ps k cs

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

parseTxt :: Text -> Either (Either Text Text) File
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
parseTerm  = parse terme

parseType :: Text -> Either Text Type
parseType = parse typee

-- parseLiftingType :: Text -> Either Text LiftingType
-- parseLiftingType = parse liftingtype

parseKind :: Text -> Either Text Kind
parseKind = parse kinde

parseDefTermOrType :: Text -> Either Text Def
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
