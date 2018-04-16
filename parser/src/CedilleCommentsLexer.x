{

module CedilleCommentsLexer where

import Data.Text(Text,pack,unpack)
import System.Environment
import Data.Maybe

}

%wrapper "monadUserState"

@any   = .
@anyNL = (. | \n) 

token :-
      <0> \-\- @any*  	        { mkLineComment      }
      <0> \{\- 	                { mkCommentBegin     } -- begin commentSart      
      <0> @anyNL 		;
      <commentStart>  \-\}      { mkCommentDecrease  } -- begin 0 if balanced
      <commentStart>  \{\-      { mkCommentIncrease  } 
      <commentStart> @anyNL 	;

{

type PosInfo = Text

data AlexUserState = AlexUserState {
     first_bracket_pos :: Int,
     num_open_brackets :: Int
}

alexInitUserState = AlexUserState {first_bracket_pos=0,num_open_brackets=0}

data Entity = EntityComment PosInfo PosInfo
            | EntityNonws
            | EntityWs  PosInfo PosInfo
  deriving (Eq,Show)
  
data Entities = EndEntity | Entity Entity Entities
  deriving (Eq,Show)

data Start = File Entities
  deriving (Eq,Show)

alexEOF :: Alex (Maybe Entity)
alexEOF = do
   state <- alexGetStartCode
   if (state == 0) then
      return $ Nothing
   else do
      alexSetStartCode 0
      user_state        <- alexGetUserState
      ((AlexPn p _ _), _ , _ , _) <- alexGetInput
      return $ Just $ EntityComment (pack $ show $ first_bracket_pos user_state) (pack $ show $ p) 

isEOF :: Maybe Entity -> Bool
isEOF = isNothing

mkLineComment :: AlexAction  (Maybe Entity)
mkLineComment ((AlexPn p _ _), _, _, _) len = return $ Just $ EntityComment (pack $ show $ p + 1) (pack $ show $ p + len + 1)

mkCommentBegin :: AlexAction (Maybe Entity)
mkCommentBegin ((AlexPn p _ _), _, _, _) _ = do
  alexSetStartCode commentStart
  alexSetUserState AlexUserState{first_bracket_pos=p+1, num_open_brackets=0}
  alexMonadScan

mkCommentIncrease :: AlexAction (Maybe Entity)
mkCommentIncrease ((AlexPn p _ _), _, _, _) len = do
  s <- alexGetUserState
  alexSetUserState s{num_open_brackets=(num_open_brackets s) + 1}
  alexMonadScan

mkCommentDecrease :: AlexAction (Maybe Entity)
mkCommentDecrease ((AlexPn p _ _), _, _, _) len = do
  s <- alexGetUserState
  if (num_open_brackets s == 0) then do
    alexSetStartCode 0
    return $ Just $ EntityComment (pack $ show $ first_bracket_pos s) (pack $ show (p+len+1))
  else do
    alexSetUserState s{num_open_brackets=(num_open_brackets s) - 1}
    alexMonadScan    

scanner :: String -> Either String Entities
scanner str = 
  let loop = do
        tok <- alexMonadScan
        if isEOF tok
          then return EndEntity
          else do toks <- loop; return (Entity (fromJust tok) toks)
  in runAlex str loop

scanComments :: Text -> Start
scanComments s = case scanner (unpack s) of
  Left _  -> File EndEntity
  Right e -> File e

main :: IO ()
main = do
  [ file ] <- getArgs
  s        <- readFile file
  case (scanner s) of
    Left msg    -> writeFile (file ++ "-result") msg
    Right tokns -> writeFile (file ++ "-result") (show tokns)

}
