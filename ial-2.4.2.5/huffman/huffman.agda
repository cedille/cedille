module huffman where

open import lib

open import huffman-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _ws-plus-10 : gratr2-nt
  _ws : gratr2-nt
  _words : gratr2-nt
  _word : gratr2-nt
  _start : gratr2-nt
  _posinfo : gratr2-nt
  _ows-star-11 : gratr2-nt
  _ows : gratr2-nt
  _digit : gratr2-nt
  _codes : gratr2-nt
  _code : gratr2-nt
  _cmd : gratr2-nt
  _character-range-2 : gratr2-nt
  _character-range-1 : gratr2-nt
  _character-bar-7 : gratr2-nt
  _character-bar-6 : gratr2-nt
  _character-bar-5 : gratr2-nt
  _character-bar-4 : gratr2-nt
  _character-bar-3 : gratr2-nt
  _character : gratr2-nt
  _bvlit : gratr2-nt
  _aws-bar-9 : gratr2-nt
  _aws-bar-8 : gratr2-nt
  _aws : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _ws-plus-10 _ws-plus-10 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _words _words = tt
gratr2-nt-eq  _word _word = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _ows-star-11 _ows-star-11 = tt
gratr2-nt-eq  _ows _ows = tt
gratr2-nt-eq  _digit _digit = tt
gratr2-nt-eq  _codes _codes = tt
gratr2-nt-eq  _code _code = tt
gratr2-nt-eq  _cmd _cmd = tt
gratr2-nt-eq  _character-range-2 _character-range-2 = tt
gratr2-nt-eq  _character-range-1 _character-range-1 = tt
gratr2-nt-eq  _character-bar-7 _character-bar-7 = tt
gratr2-nt-eq  _character-bar-6 _character-bar-6 = tt
gratr2-nt-eq  _character-bar-5 _character-bar-5 = tt
gratr2-nt-eq  _character-bar-4 _character-bar-4 = tt
gratr2-nt-eq  _character-bar-3 _character-bar-3 = tt
gratr2-nt-eq  _character _character = tt
gratr2-nt-eq  _bvlit _bvlit = tt
gratr2-nt-eq  _aws-bar-9 _aws-bar-9 = tt
gratr2-nt-eq  _aws-bar-8 _aws-bar-8 = tt
gratr2-nt-eq  _aws _aws = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


huffman-start : gratr2-nt → 𝕃 gratr2-rule
huffman-start _ws-plus-10 = (just "P71" , nothing , just _ws-plus-10 , inj₁ _aws :: inj₁ _ws-plus-10 :: []) :: (just "P70" , nothing , just _ws-plus-10 , inj₁ _aws :: []) :: []
huffman-start _ws = (just "P72" , nothing , just _ws , inj₁ _ws-plus-10 :: []) :: []
huffman-start _words = (just "WordsStart" , nothing , just _words , inj₁ _word :: []) :: (just "WordsNext" , nothing , just _words , inj₁ _word :: inj₁ _ws :: inj₁ _words :: []) :: []
huffman-start _word = (just "P1" , nothing , just _word , inj₁ _character :: inj₁ _word :: []) :: (just "P0" , nothing , just _word , inj₁ _character :: []) :: []
huffman-start _start = (just "File" , nothing , just _start , inj₁ _ows :: inj₁ _cmd :: inj₁ _ows :: []) :: []
huffman-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
huffman-start _ows-star-11 = (just "P74" , nothing , just _ows-star-11 , inj₁ _aws :: inj₁ _ows-star-11 :: []) :: (just "P73" , nothing , just _ows-star-11 , []) :: []
huffman-start _ows = (just "P75" , nothing , just _ows , inj₁ _ows-star-11 :: []) :: []
huffman-start _digit = (just "Zero" , nothing , just _digit , inj₂ '0' :: []) :: (just "One" , nothing , just _digit , inj₂ '1' :: []) :: []
huffman-start _codes = (just "CodesStart" , nothing , just _codes , inj₁ _code :: []) :: (just "CodesNext" , nothing , just _codes , inj₁ _code :: inj₁ _ws :: inj₁ _codes :: []) :: []
huffman-start _code = (just "Code" , nothing , just _code , inj₁ _word :: inj₁ _ws :: inj₂ '<' :: inj₂ '-' :: inj₁ _ws :: inj₁ _bvlit :: []) :: []
huffman-start _cmd = (just "Encode" , nothing , just _cmd , inj₁ _words :: []) :: (just "Decode" , nothing , just _cmd , inj₂ '!' :: inj₁ _ws :: inj₁ _codes :: inj₁ _ws :: inj₁ _bvlit :: []) :: []
huffman-start _character-range-2 = (just "P53" , nothing , just _character-range-2 , inj₂ 'Z' :: []) :: (just "P52" , nothing , just _character-range-2 , inj₂ 'Y' :: []) :: (just "P51" , nothing , just _character-range-2 , inj₂ 'X' :: []) :: (just "P50" , nothing , just _character-range-2 , inj₂ 'W' :: []) :: (just "P49" , nothing , just _character-range-2 , inj₂ 'V' :: []) :: (just "P48" , nothing , just _character-range-2 , inj₂ 'U' :: []) :: (just "P47" , nothing , just _character-range-2 , inj₂ 'T' :: []) :: (just "P46" , nothing , just _character-range-2 , inj₂ 'S' :: []) :: (just "P45" , nothing , just _character-range-2 , inj₂ 'R' :: []) :: (just "P44" , nothing , just _character-range-2 , inj₂ 'Q' :: []) :: (just "P43" , nothing , just _character-range-2 , inj₂ 'P' :: []) :: (just "P42" , nothing , just _character-range-2 , inj₂ 'O' :: []) :: (just "P41" , nothing , just _character-range-2 , inj₂ 'N' :: []) :: (just "P40" , nothing , just _character-range-2 , inj₂ 'M' :: []) :: (just "P39" , nothing , just _character-range-2 , inj₂ 'L' :: []) :: (just "P38" , nothing , just _character-range-2 , inj₂ 'K' :: []) :: (just "P37" , nothing , just _character-range-2 , inj₂ 'J' :: []) :: (just "P36" , nothing , just _character-range-2 , inj₂ 'I' :: []) :: (just "P35" , nothing , just _character-range-2 , inj₂ 'H' :: []) :: (just "P34" , nothing , just _character-range-2 , inj₂ 'G' :: []) :: (just "P33" , nothing , just _character-range-2 , inj₂ 'F' :: []) :: (just "P32" , nothing , just _character-range-2 , inj₂ 'E' :: []) :: (just "P31" , nothing , just _character-range-2 , inj₂ 'D' :: []) :: (just "P30" , nothing , just _character-range-2 , inj₂ 'C' :: []) :: (just "P29" , nothing , just _character-range-2 , inj₂ 'B' :: []) :: (just "P28" , nothing , just _character-range-2 , inj₂ 'A' :: []) :: []
huffman-start _character-range-1 = (just "P9" , nothing , just _character-range-1 , inj₂ 'h' :: []) :: (just "P8" , nothing , just _character-range-1 , inj₂ 'g' :: []) :: (just "P7" , nothing , just _character-range-1 , inj₂ 'f' :: []) :: (just "P6" , nothing , just _character-range-1 , inj₂ 'e' :: []) :: (just "P5" , nothing , just _character-range-1 , inj₂ 'd' :: []) :: (just "P4" , nothing , just _character-range-1 , inj₂ 'c' :: []) :: (just "P3" , nothing , just _character-range-1 , inj₂ 'b' :: []) :: (just "P27" , nothing , just _character-range-1 , inj₂ 'z' :: []) :: (just "P26" , nothing , just _character-range-1 , inj₂ 'y' :: []) :: (just "P25" , nothing , just _character-range-1 , inj₂ 'x' :: []) :: (just "P24" , nothing , just _character-range-1 , inj₂ 'w' :: []) :: (just "P23" , nothing , just _character-range-1 , inj₂ 'v' :: []) :: (just "P22" , nothing , just _character-range-1 , inj₂ 'u' :: []) :: (just "P21" , nothing , just _character-range-1 , inj₂ 't' :: []) :: (just "P20" , nothing , just _character-range-1 , inj₂ 's' :: []) :: (just "P2" , nothing , just _character-range-1 , inj₂ 'a' :: []) :: (just "P19" , nothing , just _character-range-1 , inj₂ 'r' :: []) :: (just "P18" , nothing , just _character-range-1 , inj₂ 'q' :: []) :: (just "P17" , nothing , just _character-range-1 , inj₂ 'p' :: []) :: (just "P16" , nothing , just _character-range-1 , inj₂ 'o' :: []) :: (just "P15" , nothing , just _character-range-1 , inj₂ 'n' :: []) :: (just "P14" , nothing , just _character-range-1 , inj₂ 'm' :: []) :: (just "P13" , nothing , just _character-range-1 , inj₂ 'l' :: []) :: (just "P12" , nothing , just _character-range-1 , inj₂ 'k' :: []) :: (just "P11" , nothing , just _character-range-1 , inj₂ 'j' :: []) :: (just "P10" , nothing , just _character-range-1 , inj₂ 'i' :: []) :: []
huffman-start _character-bar-7 = (just "P63" , nothing , just _character-bar-7 , inj₁ _character-bar-6 :: []) :: (just "P62" , nothing , just _character-bar-7 , inj₁ _character-range-1 :: []) :: []
huffman-start _character-bar-6 = (just "P61" , nothing , just _character-bar-6 , inj₁ _character-bar-5 :: []) :: (just "P60" , nothing , just _character-bar-6 , inj₁ _character-range-2 :: []) :: []
huffman-start _character-bar-5 = (just "P59" , nothing , just _character-bar-5 , inj₁ _character-bar-4 :: []) :: (just "P58" , nothing , just _character-bar-5 , inj₂ '(' :: []) :: []
huffman-start _character-bar-4 = (just "P57" , nothing , just _character-bar-4 , inj₁ _character-bar-3 :: []) :: (just "P56" , nothing , just _character-bar-4 , inj₂ ')' :: []) :: []
huffman-start _character-bar-3 = (just "P55" , nothing , just _character-bar-3 , inj₂ '.' :: []) :: (just "P54" , nothing , just _character-bar-3 , inj₂ ',' :: []) :: []
huffman-start _character = (just "P64" , nothing , just _character , inj₁ _character-bar-7 :: []) :: []
huffman-start _bvlit = (just "BvlitStart" , nothing , just _bvlit , inj₁ _digit :: []) :: (just "BvlitCons" , nothing , just _bvlit , inj₁ _digit :: inj₁ _bvlit :: []) :: []
huffman-start _aws-bar-9 = (just "P68" , nothing , just _aws-bar-9 , inj₁ _aws-bar-8 :: []) :: (just "P67" , nothing , just _aws-bar-9 , inj₂ '\n' :: []) :: []
huffman-start _aws-bar-8 = (just "P66" , nothing , just _aws-bar-8 , inj₂ ' ' :: []) :: (just "P65" , nothing , just _aws-bar-8 , inj₂ '\t' :: []) :: []
huffman-start _aws = (just "P69" , nothing , just _aws , inj₁ _aws-bar-9 :: []) :: []


huffman-return : maybe gratr2-nt → 𝕃 gratr2-rule
huffman-return _ = []

huffman-rtn : gratr2-rtn
huffman-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = huffman-start ; gratr2-return = huffman-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- BvlitCons-} ((Id "BvlitCons") :: (ParseTree (parsed-digit x0)) :: _::_(ParseTree (parsed-bvlit x1)) rest) = just (ParseTree (parsed-bvlit (norm-bvlit (BvlitCons x0 x1))) ::' rest , 3)
len-dec-rewrite {- BvlitStart-} ((Id "BvlitStart") :: _::_(ParseTree (parsed-digit x0)) rest) = just (ParseTree (parsed-bvlit (norm-bvlit (BvlitStart x0))) ::' rest , 2)
len-dec-rewrite {- Code-} ((Id "Code") :: (ParseTree (parsed-word x0)) :: (ParseTree parsed-ws) :: (InputChar '<') :: (InputChar '-') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-bvlit x1)) rest) = just (ParseTree (parsed-code (norm-code (Code x0 x1))) ::' rest , 7)
len-dec-rewrite {- CodesNext-} ((Id "CodesNext") :: (ParseTree (parsed-code x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-codes x1)) rest) = just (ParseTree (parsed-codes (norm-codes (CodesNext x0 x1))) ::' rest , 4)
len-dec-rewrite {- CodesStart-} ((Id "CodesStart") :: _::_(ParseTree (parsed-code x0)) rest) = just (ParseTree (parsed-codes (norm-codes (CodesStart x0))) ::' rest , 2)
len-dec-rewrite {- Decode-} ((Id "Decode") :: (InputChar '!') :: (ParseTree parsed-ws) :: (ParseTree (parsed-codes x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-bvlit x1)) rest) = just (ParseTree (parsed-cmd (norm-cmd (Decode x0 x1))) ::' rest , 6)
len-dec-rewrite {- Encode-} ((Id "Encode") :: _::_(ParseTree (parsed-words x0)) rest) = just (ParseTree (parsed-cmd (norm-cmd (Encode x0))) ::' rest , 2)
len-dec-rewrite {- File-} ((Id "File") :: (ParseTree parsed-ows) :: (ParseTree (parsed-cmd x0)) :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-start (norm-start (File x0))) ::' rest , 4)
len-dec-rewrite {- One-} ((Id "One") :: _::_(InputChar '1') rest) = just (ParseTree (parsed-digit (norm-digit One)) ::' rest , 2)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(ParseTree (parsed-character x0)) rest) = just (ParseTree (parsed-word (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: (ParseTree (parsed-character x0)) :: _::_(ParseTree (parsed-word x1)) rest) = just (ParseTree (parsed-word (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'i') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'i'))) ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'j') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'j'))) ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'k') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'k'))) ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'l') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'l'))) ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'm') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'm'))) ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'n') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'n'))) ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'o') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'o'))) ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'p') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'p'))) ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 'q') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'q'))) ::' rest , 2)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 'r') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'r'))) ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar 'a') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'a'))) ::' rest , 2)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 's') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 's'))) ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 't') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 't'))) ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 'u') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'u'))) ::' rest , 2)
len-dec-rewrite {- P23-} ((Id "P23") :: _::_(InputChar 'v') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'v'))) ::' rest , 2)
len-dec-rewrite {- P24-} ((Id "P24") :: _::_(InputChar 'w') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'w'))) ::' rest , 2)
len-dec-rewrite {- P25-} ((Id "P25") :: _::_(InputChar 'x') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'x'))) ::' rest , 2)
len-dec-rewrite {- P26-} ((Id "P26") :: _::_(InputChar 'y') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'y'))) ::' rest , 2)
len-dec-rewrite {- P27-} ((Id "P27") :: _::_(InputChar 'z') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'z'))) ::' rest , 2)
len-dec-rewrite {- P28-} ((Id "P28") :: _::_(InputChar 'A') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'A'))) ::' rest , 2)
len-dec-rewrite {- P29-} ((Id "P29") :: _::_(InputChar 'B') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'B'))) ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: _::_(InputChar 'b') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'b'))) ::' rest , 2)
len-dec-rewrite {- P30-} ((Id "P30") :: _::_(InputChar 'C') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'C'))) ::' rest , 2)
len-dec-rewrite {- P31-} ((Id "P31") :: _::_(InputChar 'D') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'D'))) ::' rest , 2)
len-dec-rewrite {- P32-} ((Id "P32") :: _::_(InputChar 'E') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'E'))) ::' rest , 2)
len-dec-rewrite {- P33-} ((Id "P33") :: _::_(InputChar 'F') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'F'))) ::' rest , 2)
len-dec-rewrite {- P34-} ((Id "P34") :: _::_(InputChar 'G') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'G'))) ::' rest , 2)
len-dec-rewrite {- P35-} ((Id "P35") :: _::_(InputChar 'H') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'H'))) ::' rest , 2)
len-dec-rewrite {- P36-} ((Id "P36") :: _::_(InputChar 'I') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'I'))) ::' rest , 2)
len-dec-rewrite {- P37-} ((Id "P37") :: _::_(InputChar 'J') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'J'))) ::' rest , 2)
len-dec-rewrite {- P38-} ((Id "P38") :: _::_(InputChar 'K') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'K'))) ::' rest , 2)
len-dec-rewrite {- P39-} ((Id "P39") :: _::_(InputChar 'L') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'L'))) ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar 'c') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'c'))) ::' rest , 2)
len-dec-rewrite {- P40-} ((Id "P40") :: _::_(InputChar 'M') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'M'))) ::' rest , 2)
len-dec-rewrite {- P41-} ((Id "P41") :: _::_(InputChar 'N') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'N'))) ::' rest , 2)
len-dec-rewrite {- P42-} ((Id "P42") :: _::_(InputChar 'O') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'O'))) ::' rest , 2)
len-dec-rewrite {- P43-} ((Id "P43") :: _::_(InputChar 'P') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'P'))) ::' rest , 2)
len-dec-rewrite {- P44-} ((Id "P44") :: _::_(InputChar 'Q') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'Q'))) ::' rest , 2)
len-dec-rewrite {- P45-} ((Id "P45") :: _::_(InputChar 'R') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'R'))) ::' rest , 2)
len-dec-rewrite {- P46-} ((Id "P46") :: _::_(InputChar 'S') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'S'))) ::' rest , 2)
len-dec-rewrite {- P47-} ((Id "P47") :: _::_(InputChar 'T') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'T'))) ::' rest , 2)
len-dec-rewrite {- P48-} ((Id "P48") :: _::_(InputChar 'U') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'U'))) ::' rest , 2)
len-dec-rewrite {- P49-} ((Id "P49") :: _::_(InputChar 'V') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'V'))) ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar 'd') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'd'))) ::' rest , 2)
len-dec-rewrite {- P50-} ((Id "P50") :: _::_(InputChar 'W') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'W'))) ::' rest , 2)
len-dec-rewrite {- P51-} ((Id "P51") :: _::_(InputChar 'X') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'X'))) ::' rest , 2)
len-dec-rewrite {- P52-} ((Id "P52") :: _::_(InputChar 'Y') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'Y'))) ::' rest , 2)
len-dec-rewrite {- P53-} ((Id "P53") :: _::_(InputChar 'Z') rest) = just (ParseTree (parsed-character-range-2 (string-append 0 (char-to-string 'Z'))) ::' rest , 2)
len-dec-rewrite {- P54-} ((Id "P54") :: _::_(InputChar ',') rest) = just (ParseTree (parsed-character-bar-3 (string-append 0 (char-to-string ','))) ::' rest , 2)
len-dec-rewrite {- P55-} ((Id "P55") :: _::_(InputChar '.') rest) = just (ParseTree (parsed-character-bar-3 (string-append 0 (char-to-string '.'))) ::' rest , 2)
len-dec-rewrite {- P56-} ((Id "P56") :: _::_(InputChar ')') rest) = just (ParseTree (parsed-character-bar-4 (string-append 0 (char-to-string ')'))) ::' rest , 2)
len-dec-rewrite {- P57-} ((Id "P57") :: _::_(ParseTree (parsed-character-bar-3 x0)) rest) = just (ParseTree (parsed-character-bar-4 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P58-} ((Id "P58") :: _::_(InputChar '(') rest) = just (ParseTree (parsed-character-bar-5 (string-append 0 (char-to-string '('))) ::' rest , 2)
len-dec-rewrite {- P59-} ((Id "P59") :: _::_(ParseTree (parsed-character-bar-4 x0)) rest) = just (ParseTree (parsed-character-bar-5 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'e') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'e'))) ::' rest , 2)
len-dec-rewrite {- P60-} ((Id "P60") :: _::_(ParseTree (parsed-character-range-2 x0)) rest) = just (ParseTree (parsed-character-bar-6 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P61-} ((Id "P61") :: _::_(ParseTree (parsed-character-bar-5 x0)) rest) = just (ParseTree (parsed-character-bar-6 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P62-} ((Id "P62") :: _::_(ParseTree (parsed-character-range-1 x0)) rest) = just (ParseTree (parsed-character-bar-7 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P63-} ((Id "P63") :: _::_(ParseTree (parsed-character-bar-6 x0)) rest) = just (ParseTree (parsed-character-bar-7 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P64-} ((Id "P64") :: _::_(ParseTree (parsed-character-bar-7 x0)) rest) = just (ParseTree (parsed-character (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P65-} ((Id "P65") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-aws-bar-8 ::' rest , 2)
len-dec-rewrite {- P66-} ((Id "P66") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-aws-bar-8 ::' rest , 2)
len-dec-rewrite {- P67-} ((Id "P67") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-aws-bar-9 ::' rest , 2)
len-dec-rewrite {- P68-} ((Id "P68") :: _::_(ParseTree parsed-aws-bar-8) rest) = just (ParseTree parsed-aws-bar-9 ::' rest , 2)
len-dec-rewrite {- P69-} ((Id "P69") :: _::_(ParseTree parsed-aws-bar-9) rest) = just (ParseTree parsed-aws ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'f') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'f'))) ::' rest , 2)
len-dec-rewrite {- P70-} ((Id "P70") :: _::_(ParseTree parsed-aws) rest) = just (ParseTree parsed-ws-plus-10 ::' rest , 2)
len-dec-rewrite {- P71-} ((Id "P71") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ws-plus-10) rest) = just (ParseTree parsed-ws-plus-10 ::' rest , 3)
len-dec-rewrite {- P72-} ((Id "P72") :: _::_(ParseTree parsed-ws-plus-10) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P74-} ((Id "P74") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ows-star-11) rest) = just (ParseTree parsed-ows-star-11 ::' rest , 3)
len-dec-rewrite {- P75-} ((Id "P75") :: _::_(ParseTree parsed-ows-star-11) rest) = just (ParseTree parsed-ows ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'g') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'g'))) ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'h') rest) = just (ParseTree (parsed-character-range-1 (string-append 0 (char-to-string 'h'))) ::' rest , 2)
len-dec-rewrite {- WordsNext-} ((Id "WordsNext") :: (ParseTree (parsed-word x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-words x1)) rest) = just (ParseTree (parsed-words (norm-words (WordsNext x0 x1))) ::' rest , 4)
len-dec-rewrite {- WordsStart-} ((Id "WordsStart") :: _::_(ParseTree (parsed-word x0)) rest) = just (ParseTree (parsed-words (norm-words (WordsStart x0))) ::' rest , 2)
len-dec-rewrite {- Zero-} ((Id "Zero") :: _::_(InputChar '0') rest) = just (ParseTree (parsed-digit (norm-digit Zero)) ::' rest , 2)
len-dec-rewrite {- P73-} (_::_(Id "P73") rest) = just (ParseTree parsed-ows-star-11 ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
