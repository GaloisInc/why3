module Language.Why3.LexerUtils where

import Data.Char(toLower)
import Data.Word(Word8)
import qualified Data.ByteString.Lazy as BS
import Data.Bits((.&.))

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

data AlexInput            = Inp { alexPos           :: !Position
                                , input             :: !BS.ByteString
                                } deriving Show

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar _ = error "We don't use left contexts"

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte i =
  do (b,bs) <- BS.uncons (input i)
     return (b, i { input = bs, alexPos = move (alexPos i) b })

-------------------------------------------------------------------------------

type Action = Position -> Text -> LexS -> (Maybe Token, LexS)

data LexS   = Normal
            | InComment Position ![Position] [Text]
            | InString Position Text

data Position = Position { line :: !Int, col :: !Int }
                deriving (Eq,Ord,Show)

move :: Position -> Word8 -> Position
move p c
  | c == toEnum (fromEnum '\t') = p { col = ((col p + 7) `div` 8) * 8 + 1 }
  | c == toEnum (fromEnum '\n') = p { col = 0, line = 1 + line p }

  -- The top 2 bits are 10...
  | c .&. 0xC0  == 0x80 {- partial byte in a char -} = p
  | otherwise = p { col = 1 + col p }

startComment :: Action
startComment p txt s = (Nothing, InComment p stack chunks)
  where
  (stack,chunks) =
    case s of
      Normal            -> ([], [txt])
      InComment q qs cs -> (q : qs, txt : cs)
      _                 -> error "[Lexer] startComment" ["in a string"]

endComent :: Action
endComent _ txt s =
  case s of
    InComment f [] cs     -> (Just (mkToken f cs), Normal)
    InComment _ (q:qs) cs -> (Nothing, InComment q qs (txt : cs))
    _                     -> error "[Lexer] endComment" ["outside commend"]
  where
  mkToken f cs = Token
    { tokenType = White BlockComment
    , tokenPos  = f
    , tokenText = Text.concat $ reverse $ txt : cs
    }

addToComment :: Action
addToComment _ txt s = (Nothing, InComment p stack (txt : chunks))
  where
  (p, stack, chunks) =
     case s of
       InComment q qs cs -> (q,qs,cs)
       _                 -> error "[Lexer] addToComment" ["outside comment"]

startString :: Action
startString p txt _ = (Nothing, InString p txt)

endString :: Action
endString _ txt s = case s of
  InString ps str -> (Just (mkToken ps str), Normal)
  _               -> error "[Lexer] endString" ["outside string"]
  where
  parseStr s1 = case reads s1 of
                  [(cs, "")] -> StrLit cs
                  _          -> Err InvalidString
  mkToken ps str = Token
    { tokenPos  = ps
    -- XXX
    , tokenType = parseStr (Text.unpack (Text.append str txt))
    , tokenText = Text.append str txt
    }

addToString :: Action
addToString _ txt s = case s of
  InString p str -> (Nothing,InString p (Text.append str txt))
  _              -> error "[Lexer] addToString" ["outside string"]

emit :: TokenT -> Action
emit t p s z  = (Just tok, z)
  where tok = Token { tokenPos = p, tokenType = t, tokenText = s }

emitS :: (Text -> TokenT) -> Action
emitS t p s z  = emit (t s) p s z



--------------------------------------------------------------------------------
-- XXX: this can be better...
numToken :: Text -> TokenT
numToken ds0 = Num (op (toVal ds)) (fromInteger rad)
  where
  (rad,ds,op) =
    case filter (/= '_') (Text.unpack ds0) of
      '0' : 'x' : more -> (16,more,id)
      '0' : 'X' : more -> (16,more,id)
      '0' : 'O' : more -> (8,more,id)
      '0' : 'o' : more -> (8,more,id)
      '0' : 'B' : more -> (2,more,id)
      '0' : 'b' : more -> (2,more,id)
      '-' :       more -> (10,more,negate)
      more             -> (10,more,id)

  toVal = sum . zipWith (\n x -> rad^n * x) [0 :: Integer ..]
              . map toDig . reverse
  toDig = if rad == 16 then fromHexDigit else fromDecDigit

fromDecDigit   :: Char -> Integer
fromDecDigit x  = read [x]

fromHexDigit :: Char -> Integer
fromHexDigit x'
  | 'a' <= x && x <= 'f'  = fromIntegral (10 + fromEnum x - fromEnum 'a')
  | otherwise             = fromDecDigit x
  where x                 = toLower x'


--------------------------------------------------------------------------------

data Token    = Token { tokenType :: TokenT
                      , tokenText :: Text
                      , tokenPos  :: Position
                      }
                deriving Show

data IdQual   = Unqual | Qual deriving (Eq,Show)
data IdCase   = Lower | Upper deriving (Eq,Show)

data TokenT   = Num Integer Int       -- ^ value, base
              | RealTok               -- ^ We don't process reals for now
              | Ident IdQual IdCase   -- ^ qualified?, classification
              | TIdent                -- ^ Theory identifier
              | StrLit Text           -- ^ string literal
              | KW    TokenKW         -- ^ keyword
              | Sym   TokenSym        -- ^ symbols
              | Op    TokenOp         -- ^ operators

              | White TokenW          -- ^ white space token
              | Err   TokenErr        -- ^ error token
              | EOF                   -- ^ End of file
                deriving (Eq,Show)

data TokenW   = BlockComment | Space
                deriving (Eq,Show)

data TokenKW  = KW_if    | KW_then | KW_else
              | KW_let   | KW_in
              | KW_match | KW_with | KW_end
              | KW_as
              | KW_forall | KW_exists | KW_not | KW_true | KW_false

              | KW_theory
              | KW_type
              | KW_constant
              | KW_function
              | KW_predicate
              | KW_inductive
              | KW_coinductive
              | KW_axiom
              | KW_lemma
              | KW_goal
              | KW_use
              | KW_clone
              | KW_namespace
              | KW_import
              | KW_export
               deriving (Eq,Show)

data TokenOp  = ArrowL | ArrowR | ArrowLR
              | AsymDisj | Disj | AsymConj | Conj
              | BangOp
              | OtherOp Int        -- operator level
                deriving (Eq,Show)

data TokenSym = Comma | Dot | Semi | Colon | Quote
              | Eq | Underscore | Bar
              | ParenL   | ParenR
              | BracketL | BracketR
              | CurlyL   | CurlyR
                deriving (Eq,Show)

data TokenErr = UnterminatedComment
              | UnterminatedString
              | UnterminatedChar
              | InvalidString
              | InvalidChar
              | LexicalError
                deriving (Eq,Show)


