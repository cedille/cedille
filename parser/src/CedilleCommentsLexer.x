{

module CedilleCommentsLexer where


import Text.Show.Unicode
import Data.Text(Text,pack,unpack)

}

%wrapper "posn"

@any   = .
@anyNL = . | \n

token :-
      <0> \-\- @any*  	        { mkToken }
      <0> \{\- @anyNL* \-\}	{ mkToken  }      
      <0> @anyNL 		;

{
type PosInfo = Text

data Entity = EntityComment Text Text
            | EntityNonws
            | EntityWs Text Text
  deriving (Eq,Show)
  
data Entities = EndEntity | Entity Entity Entities
  deriving (Eq,Show)

data Start = File Entities
  deriving (Eq,Show)

mkToken :: AlexPosn -> String -> Entity
mkToken (AlexPn p _ _) s = EntityComment (pack $ show $p+1) (pack $ show $p + length s + 1)

-- alexScanTokens :: Text -> [Entity]
scanComments :: Text -> Start
scanComments s = File (foldr Entity EndEntity (alexScanTokens (unpack s)))

showStart :: Start -> Text
showStart = pack . show

}
