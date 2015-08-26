{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
module Language.Why3.PP (ppTh, ppD, ppE, ppT, ppL, ppP, isOpWhy3) where

import Language.Why3.AST
import Text.PrettyPrint
import           Data.Text (Text)
import qualified Data.Text as Text

ppTh :: Theory -> Doc
ppTh (Theory x ds) = text "theory" <+> ppText x
                  $$ vcat (map ppD ds) $$ text "end"

ppD :: Decl -> Doc
ppD decl =
  case decl of
    Use mb x mbAs -> text "use" <+> opt ppImpExp mb <+> ppText x
                                                    <+> opt ppAs mbAs

    Goal x e  -> text "goal"  <+> ppText x <> colon <+> ppE e
    Axiom x e -> text "axiom" <+> ppText x <> colon <+> ppE e
    Lemma x e -> text "lemma" <+> ppText x <> colon <+> ppE e


    Predicate x _ ts -> text "predicate" <+> ppText x
                                         <+> fsep (map (ppPrecT 1) ts)
    PredicateDef x _ ps e -> text "predicate" <+> ppText x
                          <+> fsep (map ppParam ps)
                          <+> text "=" <+> ppE e

    Function x _ [] t -> text "constant" <+> ppText x <> colon <+> ppT t
    Function x _ ts t -> text "function" <+> ppText x
                          <+> fsep (map (ppPrecT 1) ts)
                          <+> colon <+> ppT t

    FunctionDef x _ [] t e -> text "constant" <+> ppText x
                           <> colon <+> ppT t
                          <+> text "=" <+> ppE e

    FunctionDef x _ ps t e -> text "function" <+> ppText x
                          <+> fsep (map ppParam ps)
                          <+> colon <+> ppT t
                          <+> text "=" <+> ppE e

    Type x _ tvs       -> text "type" <+> ppText x <+> fsep (map ppTV tvs)
    TypeDef x _ tvs ty -> text "type" <+> ppText x <+> fsep (map ppTV tvs) <+>
                          text "=" <+>
                          case ty of
                            Ty t        -> ppT t
                            TyRecord fs ->
                               braces $ vcat $ punctuate (char ';') $ map ppF fs
                            TyCase tcs -> vcat $ map ppTyCaseAlt tcs



  where
  ppF (x,t) = ppText x <> colon <+> ppT t

  ppTV (x,_) = text "'" <> ppText x

  ppParam (Nothing, t) = ppPrecT 1 t
  ppParam (Just x, t)  = parens (ppText x <> colon <+> ppT t)

  opt _ Nothing   = empty
  opt f (Just x)  = f x

  ppImpExp Import = text "import"
  ppImpExp Export = text "export"

  ppAs x = text "as" <+> ppText x

  ppTyCaseAlt (TyCaseAlt x _ as) = text "|" <+> ppText x
                                            <+> fsep (map ppParam as)

ppL :: Literal -> Doc
ppL lit =
  case lit of
    Integer n -> if n < 0 then parens (integer n) else integer n
    Real x    -> ppText x
    Bool b    -> text (if b then "true" else "false")

isOpWhy3 :: Name -> Maybe Int
isOpWhy3 x
  | Text.any (`elem` op1) x = Just 1
  | Text.any (`elem` op2) x = Just 2
  | Text.any (`elem` op3) x = Just 3
  | Text.any (`elem` op4) x = Just 4
  | otherwise          = Nothing
  where
  op1 = ['=', '<', '>', '~' ]
  op2 = ['+', '-' ]
  op3 = ['*', '/', '%' ]
  op4 = ['!', '$', '&', '?', '@', '^', '.', ':', '|', '#' ]



ppE :: Expr -> Doc
ppE = go 0
  where
  go prec expr =
    case expr of
      Lit l -> ppL l
      App x [e1, e2]
       | Just n <- isOpWhy3 x
       , let lP = case e1 of
                    App {} -> n - 1
                    _      -> n   -- (e.g., if we have `if` on the left0

       -> wrap n prec (go lP e1 <+> ppText x <+> go n e2)
      App "[]" [e1, e2]       -> wrap 6 prec (go 5 e1 <> brackets (go 0 e2))
      App "[<-]" [e1, e2, e3] ->
        wrap 6 prec (go 5 e1 <> brackets (go 0 e2 <+> text "<-" <+> go 0 e3))
      App x []                -> ppText x
      App x es                -> wrap 5 prec (ppText x <+> fsep (map (go 5) es))
      Let p e1 e2             ->
        wrap 1 prec (text "let" <+> ppP p <+> text "=" <+>
                                          go 0 e1 <+> text "in" $$ go 0 e2)
      If e1 e2 e3             -> wrap 1 prec
          (text "if" <+> go 0 e1
                $$ nest 2 (text "then" <+> go 0 e2 $$
                           text "else" <+> go 0 e3))
      Match es alts -> wrap 1 prec
        ( text "match"
          <+> fsep (punctuate comma (map (go 0) es))
          <+> text "with"
          $$ nest 2 (vcat (map ppAlt alts))
        )
        where ppAlt (p,e) = text "|" <+> ppP p <+> text "->" <+> go 0 e
      Conn Implies _ _ ->
        wrap 1 prec (vcat [ go 1 e <+> text "->" | e <- xs ]
                                        $$ go 1 y)
        where splitImp (Conn Implies e1 e2) = let (xs',y') = splitImp e2
                                              in (e1:xs',y')
              splitImp e = ([],e)
              (xs,y)     = splitImp expr

      Conn c e1 e2 -> wrap 1 prec (go 1 e1 <+> text ct <+> go 1 e2)
        where ct = case c of
                     And     -> "/\\"
                     AsymAnd -> "&&"
                     Or      -> "\\/"
                     AsymOr  -> "||"
                     Implies -> "->"
                     Iff     -> "<->"


      Record fs       -> braces (sep [ ppText x <+> text "=" <+> go 0 e
                                                            | (x,e) <- fs ])
      RecordUpdate r fs -> braces (go 0 r <+> text "with" <+>
                              sep [ ppText x <+> text "=" <+> go 0 e
                                  | (x,e) <- fs ])
      Not  e           -> wrap 2 prec (text "not" <+> go 2 e)
      Field l e        -> wrap 2 prec (go 1 e <> text "." <> ppText l)
      Cast e t         -> wrap 1 prec (go 0 e <+> text ":" <+> ppT t)
      Labeled l e      -> wrap 1 prec (text (show l) <+> go 1 e)
      Quant q xs trigs e -> wrap 1 prec $
          qd <+> fsep (punctuate comma $ map param xs) <+> trds <> text "."
                                                       <+> go 0 e
        where qd = case q of
                     Forall -> text "forall"
                     Exists -> text "exists"
              param (x,t) = ppText x <> colon <+> ppT t
              trds = case trigs of
                       [] -> empty
                       _  -> brackets $ fsep
                                      $ punctuate (text "|")
                                      $ map ppTrig trigs
              ppTrig = fsep . punctuate comma . map ppE

ppP :: Pattern -> Doc
ppP = ppPrecP 0

ppPrecP :: Int -> Pattern -> Doc
ppPrecP prec pat =
  case pat of
    PWild     -> text "_"
    PVar x    -> ppText x
    PCon c [] -> ppText c
    PCon c ps -> wrap 1 prec $ ppText c <+> fsep (map (ppPrecP 1) ps)

ppT :: Type -> Doc
ppT = ppPrecT 0

ppPrecT :: Int -> Type -> Doc
ppPrecT prec ty =
    case ty of
      TyCon x []  -> ppText x
      TyCon x ts  -> wrap 1 prec (ppText x <+> hsep (map (ppPrecT 1) ts))
      TyVar a     -> text "'" <> ppText a
      Tuple ts    -> parens (hsep $ map (ppPrecT 0) ts)

wrap :: Int -> Int -> Doc -> Doc
wrap n prec d = if prec >= n then parens d else d

ppText :: Text -> Doc
ppText = text . Text.unpack
