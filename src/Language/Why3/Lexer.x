-- vim: ft=haskell
{
-- At present Alex generates code with too many warnings.
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w #-}
module Language.Why3.Lexer
  ( primLexer, lexer
  , Token(..), TokenT(..)
  , IdQual(..), IdCase(..)
  , TokenKW(..), TokenErr(..), TokenOp(..), TokenSym(..), TokenW(..)
  , Position(..)
  ) where

import Language.Why3.LexerUtils
import qualified Data.ByteString.Lazy as BS
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T
}

$lalpha       = [a-z_]
$ualpha       = [A-Z]
$digit        = [0-9]
$alpha        = [$lalpha$ualpha]
$identNext    = [$alpha$digit ']
$bin_digit    = [0-1]
$oct_digit    = [0-7]
$hex_digit    = [0-9a-fA-f]

$op_char_1    = [ \= \< \> \~ ]
$op_char_2    = [ \+ \- ]
$op_char_3    = [ \* \/ \% ]
$op_char_4    = [ \! \$ \& \? \@ \^ \. \: \| \# ]
$op_char      = [ op_char_1 op_char_2 op_char_3 op_char_4 ]

@lident       = $lalpha $identNext*
@uident       = $ualpha $identNext*
@uqualid      = (@uident \.)+ @uident
@lqualid      = (@uident \.)+ @lident
@tqualid      = ((@uident | @lident) \.)+ @uident

@integer      = \- ? $digit ( $digit | _ )*
              | 0 (x|X) $hex_digit ($hex_digit | _)*
              | 0 (o|O) $oct_digit ($oct_digit | _)*
              | 0 (b|B) $bin_digit ($bin_digit | _)*

@exponent     = (e|E) (\-|\+)? $digit +

@real         = $digit + @exponent
              | $digit + \. $digit * @exponent ?
              | $digit * \. $digit + @exponent ?

@bang_op      = \! op_char_4* | \? op_char_4*
@op4          = $op_char_4 +
@op3          = ($op_char_3 | $op_char_4) +
@op2          = ($op_char_2 | $op_char_3 | $op_char_4) +
@op1          = ($op_char_1 | $op_char_2 | $op_char_3 | $op_char_4) +




@strPart      = [^\\\"]+

:-

<0,comment> "(*"          { startComment }

<comment> {
"*)"                      { endComent }
.                         { addToComment }
\n                        { addToComment }
}


<string> {
@strPart                  { addToString }
\"                        { endString }
\\.                       { addToString }
}


<0> {
$white+                   { emit $ White Space }
\"                        { startString }

"["                        { emit $ Sym BracketL}
"]"                        { emit $ Sym BracketR }
"("                        { emit $ Sym ParenL }
")"                        { emit $ Sym ParenR }
"{"                        { emit $ Sym CurlyL }
"}"                        { emit $ Sym CurlyR }
":"                        { emit $ Sym Colon  }
"'"                        { emit $ Sym Quote  }
","                        { emit $ Sym Comma  }
"."                        { emit $ Sym Dot    }
";"                        { emit $ Sym Semi   }
"|"                        { emit $ Sym Bar    }
"_"                        { emit $ Sym Underscore }
"="                        { emit $ Sym Eq }

"<-"                       { emit $ Op ArrowL }
"->"                       { emit $ Op ArrowR }
"<->"                      { emit $ Op ArrowLR }
"||"                       { emit $ Op AsymDisj }
"\/"                       { emit $ Op Disj }
"&&"                       { emit $ Op AsymConj }
"/\"                       { emit $ Op Conj }

"as"                       { emit $ KW KW_as    }

"if"                       { emit $ KW KW_if    }
"then"                     { emit $ KW KW_then  }
"else"                     { emit $ KW KW_else  }
"let"                      { emit $ KW KW_let   }
"in"                       { emit $ KW KW_in    }
"match"                    { emit $ KW KW_match }
"with"                     { emit $ KW KW_with  }
"end"                      { emit $ KW KW_end   }

"not"                      { emit $ KW KW_not    }
"forall"                   { emit $ KW KW_forall }
"exists"                   { emit $ KW KW_exists }
"true"                     { emit $ KW KW_true   }
"false"                    { emit $ KW KW_false  }

"theory"                   { emit $ KW KW_theory }
"type"                     { emit $ KW KW_type }
"constant"                 { emit $ KW KW_constant }
"function"                 { emit $ KW KW_function }
"predicate"                { emit $ KW KW_predicate }
"inductive"                { emit $ KW KW_inductive }
"coinductive"              { emit $ KW KW_coinductive }
"axiom"                    { emit $ KW KW_axiom }
"lemma"                    { emit $ KW KW_lemma }
"goal"                     { emit $ KW KW_goal }
"use"                      { emit $ KW KW_use }
"clone"                    { emit $ KW KW_clone }
"namespace"                { emit $ KW KW_namespace }
"import"                   { emit $ KW KW_import }
"export"                   { emit $ KW KW_export }


@integer                   { emitS numToken }
@real                      { emit RealTok }

@lident                    { emit $ Ident Unqual Lower }
@uident                    { emit $ Ident Unqual Upper }
@lqualid                   { emit $ Ident Qual   Lower }
@uqualid                   { emit $ Ident Qual   Upper }
@tqualid                   { emit $ TIdent }

@bang_op                   { emit $ Op $ BangOp }
@op4                       { emit $ Op $ OtherOp 4 }
@op3                       { emit $ Op $ OtherOp 3 }
@op2                       { emit $ Op $ OtherOp 2 }
@op1                       { emit $ Op $ OtherOp 1 }
}


{
-- This code is here because it depends on `comment`, which is defined
-- in this file.

stateToInt :: LexS -> Int
stateToInt Normal         = 0
stateToInt (InComment {}) = comment
stateToInt (InString {})  = string

lexer :: BS.ByteString -> [Token]
lexer = filter nonWhite . primLexer
  where nonWhite t = case tokenType t of
                       White _ -> False
                       _       -> True

primLexer :: BS.ByteString -> [Token]
primLexer cs = run inp Normal
  where
  inp = Inp { alexPos           = Position 1 0
            , input             = cs
            }

  run i s =
    case alexScan i (stateToInt s) of
      AlexEOF ->
        case s of

          Normal -> [ Token { tokenPos = alexPos i
                            , tokenType = EOF
                            , tokenText = "(end of file)"
                            }
                    ]

          InComment p _ _ ->
              [ Token { tokenPos  = p
                      , tokenType = Err UnterminatedComment
                      , tokenText = "(unterminated comment)"
                      }
              ]

          InString p _ ->
              [ Token { tokenPos = p
                      , tokenType = Err UnterminatedString
                      , tokenText = "(unterminated string)"
                      }
              ]

      AlexError i'  ->
        [ Token { tokenPos  = alexPos i'
                , tokenType = Err LexicalError
                , tokenText = "(unexpected symbol)"
                }
        ]

      AlexSkip i' _ -> run i' s

      AlexToken i' l act ->
        let txt         = T.decodeUtf8 $ BS.take (fromIntegral l) $ input i
            (mtok,s')   = act (alexPos i) txt s
        in case mtok of
             Nothing  -> run i' $! s'
             Just t   -> t : (run i' $! s')

}



