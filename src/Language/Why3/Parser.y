-- vim: ft=haskell
{
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Why3.Parser
  ( parse
  , ParseM
  , theories
  , expr
  , pType
  ) where

import           Language.Why3.AST
import           Language.Why3.Lexer

import qualified Data.ByteString.Lazy as BS
import qualified Data.Text.Lazy as Lazy
import           Data.Text ( Text )
import qualified Data.Text as Text
import           Control.Monad(liftM,ap)
import qualified Control.Applicative as A
}


%token
  INTEGER     { Token { tokenType = Num $$ _ } }
  REAL        { Token { tokenType = RealTok, tokenText = Lazy.toStrict -> $$ } }
  STR         { Token { tokenType = StrLit (Lazy.toStrict -> $$) } }

  LIDENT      { Token { tokenType = Ident Unqual Lower, tokenText = Lazy.toStrict -> $$ } }
  UIDENT      { Token { tokenType = Ident Unqual Upper, tokenText = Lazy.toStrict -> $$ } }
  QLIDENT     { Token { tokenType = Ident Qual   Lower, tokenText = Lazy.toStrict -> $$ } }
  QUIDENT     { Token { tokenType = Ident Qual   Upper, tokenText = Lazy.toStrict -> $$ } }
  TQUALID     { Token { tokenType = TIdent,             tokenText = Lazy.toStrict -> $$ } }

  BANG_OP     { Token { tokenType = Op BangOp,      tokenText = Lazy.toStrict -> $$ } }
  OP4         { Token { tokenType = Op (OtherOp 4), tokenText = Lazy.toStrict -> $$ } }
  OP3         { Token { tokenType = Op (OtherOp 3), tokenText = Lazy.toStrict -> $$ } }
  OP2         { Token { tokenType = Op (OtherOp 2), tokenText = Lazy.toStrict -> $$ } }
  OP1         { Token { tokenType = Op (OtherOp 1), tokenText = Lazy.toStrict -> $$ } }

  '['         { Token { tokenType = Sym BracketL, tokenPos = $$ }}
  ']'         { Token { tokenType = Sym BracketR, tokenPos = $$ }}
  '('         { Token { tokenType = Sym ParenL  , tokenPos = $$ }}
  ')'         { Token { tokenType = Sym ParenR  , tokenPos = $$ }}
  '{'         { Token { tokenType = Sym CurlyL  , tokenPos = $$ }}
  '}'         { Token { tokenType = Sym CurlyR  , tokenPos = $$ }}
  '_'         { Token { tokenType = Sym Underscore, tokenPos = $$ }}
  '='         { Token { tokenType = Sym Eq, tokenPos = $$ }}
  '\''        { Token { tokenType = Sym Quote, tokenPos = $$ }}
  ','         { Token { tokenType = Sym Comma, tokenPos = $$ }}
  '.'         { Token { tokenType = Sym Dot, tokenPos = $$ }}
  ':'         { Token { tokenType = Sym Colon, tokenPos = $$ }}
  ';'         { Token { tokenType = Sym Semi, tokenPos = $$ }}
  '|'         { Token { tokenType = Sym Bar, tokenPos = $$ }}

  '<-'        { Token { tokenType = Op ArrowL, tokenPos = $$ }}
  '->'        { Token { tokenType = Op ArrowR, tokenPos = $$ }}
  '<->'       { Token { tokenType = Op ArrowLR, tokenPos = $$ }}

  'theory'    { Token { tokenType = KW KW_theory, tokenPos = $$ }}
  'end'       { Token { tokenType = KW KW_end,    tokenPos = $$ }}
  'goal'      { Token { tokenType = KW KW_goal,   tokenPos = $$ }}
  'use'       { Token { tokenType = KW KW_use,    tokenPos = $$ }}
  'import'    { Token { tokenType = KW KW_import, tokenPos = $$ }}
  'export'    { Token { tokenType = KW KW_export, tokenPos = $$ }}
  'predicate' { Token { tokenType = KW KW_predicate, tokenPos = $$ }}
  'function'  { Token { tokenType = KW KW_function, tokenPos = $$ }}
  'constant'  { Token { tokenType = KW KW_constant, tokenPos = $$ }}
  'axiom'     { Token { tokenType = KW KW_axiom, tokenPos = $$ }}
  'lemma'     { Token { tokenType = KW KW_lemma, tokenPos = $$ }}
  'type'      { Token { tokenType = KW KW_type, tokenPos = $$ }}
  'with'      { Token { tokenType = KW KW_with, tokenPos = $$ }}
  'as'        { Token { tokenType = KW KW_as,     tokenPos = $$ }}

  'true'      { Token { tokenType = KW KW_true,  tokenPos = $$ }}
  'false'     { Token { tokenType = KW KW_false, tokenPos = $$ }}
  'forall'    { Token { tokenType = KW KW_forall,tokenPos = $$ }}
  'exists'    { Token { tokenType = KW KW_exists,tokenPos = $$ }}
  'not'       { Token { tokenType = KW KW_not,   tokenPos = $$ }}
  '\\/'       { Token { tokenType = Op Disj,     tokenPos = $$ }}
  '||'        { Token { tokenType = Op AsymDisj, tokenPos = $$ }}
  '/\\'       { Token { tokenType = Op Conj,     tokenPos = $$ }}
  '&&'        { Token { tokenType = Op AsymConj, tokenPos = $$ }}

  'if'        { Token { tokenType = KW KW_if, tokenPos = $$ }}
  'match'     { Token { tokenType = KW KW_match, tokenPos = $$ }}
  'then'      { Token { tokenType = KW KW_then, tokenPos = $$ }}
  'else'      { Token { tokenType = KW KW_else, tokenPos = $$ }}
  'let'       { Token { tokenType = KW KW_let, tokenPos = $$ }}
  'in'        { Token { tokenType = KW KW_in, tokenPos = $$ }}


%name theories theories
%name theory theory
%name pType type
%name expr expr
%tokentype { Token }
%monad     { ParseM }
%lexer     { lexerP } { Token { tokenType = EOF } }

%nonassoc QUALID
%nonassoc QUANT
%nonassoc LET IF
%nonassoc LABEL
%right '->' '<->'
%right '\\/' '||'
%right '/\\' '&&'
%nonassoc 'not'
%left OP1 '='
%left OP2
%left OP3
%left OP4 '.' ':'
%nonassoc PREFIX_OP
%left APP
%nonassoc '['
%nonassoc BANG_OP

%%

--------------------------------------------------------------------------------

theories :: { [Theory] }
  : theories_rev            { reverse $1 }

theories_rev :: { [Theory] }
  :                         { [] }
  | theories_rev theory     { $2 : $1 }

theory :: { Theory }
  : 'theory' uident decls 'end' { Theory $2 (reverse $3) }

decls :: { [Decl] }
  :                         { [] }
  | decls decl              { $2 : $1 }

-- XXX: A lot of these are missing the 'with' part
decl :: { Decl }
  : 'use' imp_exp tqualid opt_as  { Use $2 $3 $4 }
  | 'predicate' lident labels type_params
                                  { Predicate $2 $3 (map snd $4) }
  | 'predicate' lident labels type_params '=' expr
                                  { PredicateDef $2 $3 $4 $6 }
  | 'function'  lident labels type_params ':' type
                                  { Function $2 $3 (map snd $4) $6 }
  | 'function'  lident labels type_params ':' type '=' expr
                                  { FunctionDef $2 $3 $4 $6 $8 }
  | 'constant' lident labels ':' type
                                  { Function $2 $3 [] $5 }
  | 'constant' lident labels ':' type '=' expr
                                  { FunctionDef $2 $3 [] $5 $7 }

  | 'axiom' ident ':' expr        { Axiom $2 $4 }
  | 'lemma' ident ':' expr        { Lemma $2 $4 }
  | 'goal'  ident ':' expr        { Goal $2 $4 }

  | 'type' lident labels tyvars   { Type $2 $3 $4 }
  | 'type' lident labels tyvars '=' type_defn{ TypeDef $2 $3 $4 $6 }


imp_exp :: { Maybe ImpExp }
  : 'import'                      { Just Import }
  | 'export'                      { Just Export }
  | {- empty -}                   { Nothing }

opt_as :: { Maybe Name }
  : {- empty -}                   { Nothing }
  | 'as' uident                   { Just $2 }

--------------------------------------------------------------------------------
-- Types

type_defn :: { TypeDef }
   : type                     { Ty $1 }
   | '{' rec_fields '}'       { TyRecord $ reverse $2 }
   | opt_bar type_cases       { TyCase (reverse $2) }

opt_bar :: { () }
opt_bar
  : '|'                       { () }
  | {- empty -}               { () }

-- reversed
type_cases :: { [TyCaseAlt] }
  : type_case                 { [$1] }
  | type_cases '|' type_case  { $3 : $1 }

type_case :: { TyCaseAlt }
  : uident labels type_params { TyCaseAlt $1 $2 $3 }

-- reversed
rec_fields :: { [(Name,Type)] }
  : rec_field                     { [$1] }
  | rec_fields ';' rec_field      { $3 : $1 }

rec_field :: { (Name,Type) }
  : lident ':' type               { ($1, $3) }

type :: { Type }
  : lqualid typeAs      { TyCon $1 (reverse $2) }
  | typeA               { $1 }

typeA :: { Type }
  : '\'' lident         { TyVar $2 }
  | lqualid             { TyCon $1 [] }
  | '(' type ')'        { $2 }
  | '(' ')'             { Tuple [] }
  | '(' types2 ')'      { Tuple (reverse $2) }

typeAs :: { [Type] }
  : typeA               { [$1] }
  | typeAs typeA        { $2 : $1 }

-- reversed
types2 :: { [Type] }
  : type ',' type       { [$3, $1] }
  | types2 ',' type     { $3 : $1 }

-- reversed
tyvars :: { [(Name, [Text])] }
  : {- empty -}               { [] }
  | tyvars '\'' lident labels { ($3,$4) : $1 }

-- NOT reversed
type_params :: { [(Maybe Name, Type)] }
  : {- empty -}              { [] }
  | type_params type_param   { $1 ++ $2 }

-- NOT reversed!
type_param :: { [ (Maybe Name, Type) ] }
  : typeA                    { [ (Nothing, $1) ] }

  {- HACKERY:
  Next is the case for:  `x y z : Int`
  It is parsed like this so tha we can decide what to do with 1 look ahead.
  Technically, this is not fully correct because we'll also accept things like:
  `x (y) : Int` but it seems close enough. -}
  | '(' type ':' type ')'    {% mkTypeParam $2 >>= \xs -> return
                                                  [ (Just x, $4) | x <- xs ] }



--------------------------------------------------------------------------------
-- Names

opt_label :: { Maybe Text }
  : STR                           { Just $1 }
  | {- empty -}                   { Nothing }

labels :: { [ Text ] }
  : labelsRev                     { reverse $1 }

-- reverse
labelsRev :: { [ Text ] }
  : {- empty -}                   { [] }
  | labelsRev STR                    { $2 : $1 }

ident :: { Name }
  : LIDENT opt_label              { $1 }
  | UIDENT opt_label              { $1 }


lident :: { Name }
  : LIDENT                        { $1 }

lidents1 :: { [Name] }
  : lident                        { [$1] }
  | lidents1 lident               { $2 : $1 }

uident :: { Name }
  : UIDENT                        { $1 }

lqualid :: { Name }
  : LIDENT                        { $1 }
  | QLIDENT                       { $1 }

uqualid :: { Name }
  : UIDENT                        { $1 }
  | QUIDENT                       { $1 }

prefix_op :: { Name }
  : OP1                           { $1 }
  | OP2                           { $1 }
  | OP3                           { $1 }
  | OP4                           { $1 }

qualid :: { Name }
  : uqualid                       { $1 }
  | lqualid %prec QUALID          { $1 }

tqualid
  : uqualid                       { $1 }
  | TQUALID                       { $1 }

--------------------------------------------------------------------------------

expr :: { Expr }
  : exprA                           { $1 }
  | qualid exprAs1                  { App $1 (reverse $2) }
  | prefix_op expr %prec PREFIX_OP  { App $1 [$2] }
  | expr '=' expr                   { App "=" [$1, $3] }
  | expr OP1 expr                   { App $2 [$1, $3] }
  | expr OP2 expr                   { App $2 [$1, $3] }
  | expr OP3 expr                   { App $2 [$1, $3] }
  | expr OP4 expr                   { App $2 [$1, $3] }
  | expr '.' lqualid                { Field $3 $1 }

  | 'if' expr 'then' expr
              'else' expr %prec IF  { If $2 $4 $6 }

  | 'match' revExprs1 'with' opt_bar
    revExprCases 'end'              { Match (reverse $2) (reverse $5) }

  | 'let' pattern '=' expr
    'in' expr      %prec LET        { Let $2 $4 $6 }

  | expr '->'  expr                 { Conn Implies $1 $3 }
  | expr '<->' expr                 { Conn Iff $1 $3 }
  | expr '/\\'  expr                { Conn And $1 $3 }
  | expr '&&'  expr                 { Conn AsymAnd $1 $3 }
  | expr '\\/'  expr                { Conn Or $1 $3 }
  | expr '||'  expr                 { Conn AsymOr $1 $3 }
  | expr ':' type                   { Cast $1 $3 }
  | STR expr %prec LABEL            { Labeled $1 $2 }
  | 'not' expr                      { Not $2 }
  | quant binders1 opt_trig '.' expr %prec QUANT
                                    { Quant $1 (concat (reverse $2)) $3 $5 }



quant :: { Quant }
  : 'forall'                        { Forall }
  | 'exists'                        { Exists }

binder :: { [(Name,Type)] }
  : lidents1 ':' type               { [ (x,$3) | x <- reverse $1 ] }

binders1 :: { [[(Name,Type)]] }
  : binder                          { [$1] }
  | binders1 ',' binder             { $3 : $1 }

opt_trig :: { [[Expr]] }
  : {- empty -}                     { [] }
  | '[' triggers ']'                { reverse $2 }

triggers :: { [[Expr]] }
  : trigger                         { [reverse $1] }
  | triggers '|' trigger            { reverse $3 : $1 }

trigger :: { [Expr] }
  : expr                            { [$1] }
  | trigger ',' expr                { $3 : $1 }

exprA :: { Expr }
  : INTEGER                         { Lit $ Integer $1 }
  | REAL                            { Lit $ Real $1 }
  | 'true'                          { Lit $ Bool True }
  | 'false'                         { Lit $ Bool False }
  | qualid                          { App $1 [] }
  | BANG_OP exprA                   { App $1 [$2] }
  | exprA '[' expr ']'              { App "[]" [$1, $3] }
  | exprA '[' expr '<-' expr ']'    { App "[<-]" [$1, $3, $5] }
  | '(' expr ')'                    { $2 }
  | '{' term_fields1 '}'            { Record (reverse $2) }
  -- TODO: not properly implemented
  | '{' expr 'with' term_fields1 '}' { RecordUpdate $2 (reverse $4) }

-- reversed
term_fields1 :: { [(Name,Expr)] }
  : term_field                      { [$1] }
  | term_fields1 ';' term_field     { $3 : $1 }

term_field :: { (Name, Expr) }
term_field
  : lqualid '=' expr                { ($1,$3) }

-- reversed
exprAs1 :: { [Expr] }
  : exprA                           { [$1] }
  | exprAs1 exprA                   { $2 : $1 }

pattern :: { Pattern }
  : patternA                        { $1 }
  | uident revPatternAs1            { PCon $1 (reverse $2) }

patternA :: { Pattern }
  : '_'                             { PWild }
  | lident                          { PVar $1 }
  | uident                          { PCon $1 [] }
  | '(' pattern ')'                 { $2 }

revPatternAs1 :: { [Pattern] }
  : patternA                         { [$1] }
  | revPatternAs1 patternA           { $2 : $1 }

revExprs1 :: { [Expr] }
  : expr                            { [$1] }
  | revExprs1 ',' expr              { $3 : $1 }

revExprCases :: { [(Pattern, Expr)] }
  : exprCase                        { [$1] }
  | revExprCases '|' exprCase       { $3 : $1 }

exprCase :: { (Pattern,Expr) }
  : pattern '->' expr               { ($1, $3) }

{

mkTypeParam :: Type -> ParseM [Name]
mkTypeParam ty =
  case ty of
    TyCon x ts | notQual x && all simpleTyCon ts ->
        return (x : [ y | TyCon y [] <- ts ])
    _ -> fail "Malformed type-parameters"
  where
  simpleTyCon (TyCon x []) = notQual x
  simpleTyCon _            = False
  notQual nm               = not (Text.any (== '.') nm)

textPos :: Position -> String
textPos p = show (line p) ++ ":" ++ show (col p)

happyError :: ParseM a
happyError = P $ \ts ->
  Left $ "Parser error around " ++
  case ts of
    t : _ -> textPos (tokenPos t)
    []    -> "the end of the file"

data ParseM a   = P { unP :: [Token] -> Either String (a,[Token]) }

instance Functor ParseM where
  fmap = liftM

instance A.Applicative ParseM where
  pure  = return
  (<*>) = ap

instance Monad ParseM where
  return a  = P (\x -> Right (a,x))
  fail x    = P (\_ -> Left x)
  P m >>= f = P (\x -> case m x of
                         Left err -> Left err
                         Right (a,y)  -> unP (f a) y)


lexerP :: (Token -> ParseM a) -> ParseM a
lexerP k = P $ \ts ->
  case ts of
    Token { tokenType = Err e, tokenText = txt } : _ ->
      Left $
        case e of
          UnterminatedComment -> "unterminated comment"
          UnterminatedString  -> "unterminated string"
          UnterminatedChar    -> "unterminated character"
          InvalidString       -> "invalid string literal: " ++ Lazy.unpack txt
          LexicalError        -> "unexpected symbol"

    t : more -> unP (k t) more
    []       -> Left "unexpected end of file"

parse :: ParseM a -> BS.ByteString -> Either String a
parse p txt = case unP p (lexer txt) of
                Left err -> Left err
                Right (a,_) -> Right a

}
