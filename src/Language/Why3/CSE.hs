{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Why3.CSE where

import            Language.Why3.AST
import            Language.Why3.Names(apSubst,countUses)

import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.List(sortBy)
import           Data.Ord(comparing)
import           MonadLib


-- | The `Int` is the seed to generate names.
-- If `cseFormula` is called multiple times, one should take care to supply
-- a new name seed, to avoid clashing names.
cseFormula :: (Int,Expr) -> (Int,Expr)
cseFormula (startName,e) =
  let (e1,k) = runLift $ runStateT k0 $ importFormula e
  in ( sNext k
     , snd
     $ foldr mkLet (countUses e1, e1)
     $ sortBy (comparing defTime)
     $ Map.toList
     $ sMap k
     )
  where
  k0                        = S { sMap = Map.empty, sNext = startName }
  defTime (_,(i,_))         = i

  mkLet (d,(_,~(App i _))) (useMap,e1) =
    let newUses = Map.unionWith (+) (countUses d) (Map.delete i useMap)
    in ( newUses
       , case Map.lookup i useMap of
           Just 1 -> apSubst (Map.singleton i d) e1
           _      -> Let (PVar i) d e1
       )


type Shape  = Expr    -- Sub-expressions are all variable or literal
type Simple = Expr    -- A variable or literal

data S = S { sMap   :: !(Map Shape (Int,Simple))
           , sNext  :: !Int
           } deriving Show

type M = StateT S Lift

importFormula :: Expr -> M Expr
importFormula expr =
  case expr of
    Lit (Bool {}) -> return expr
    Lit _         -> error "Not a formula: non-boolean literal"

    App x es ->
      do ts <- mapM importTerm es
         return $ seq x (App x ts)

    If e1 e2 e3 ->
      do e1' <- importFormula e1
         e2' <- importFormula e2
         e3' <- importFormula e3
         return (If e1' e2' e3')

    Let p e1 e2   ->
      case p of
        PWild   -> importFormula e2
        PVar x  -> do e1' <- importTerm e1
                      let su = Map.singleton x e1'
                      importFormula (apSubst su e2)

        PCon {} -> do e1' <- importTerm e1
                      e2' <- importFormula e2
                      return (Let p e1' e2')

    -- XXX: No sharing across qunatifiers.
    Quant q xs ts e ->
      do k <- get
         case cseFormula (sNext k, e) of
           (sNext', e') ->
              do set $! k { sNext = sNext' }
                 return (Quant q xs ts e')

    Field {}      -> error "Not a formula: field"
    Record {}     -> error "Not a formula: record"
    RecordUpdate {} -> error "Not a formula: record update"
    Cast {}       -> error "Not a formula: cast"
    Match {}      -> error "Not a formula: match"

    Labeled l e   ->
      do e' <- importFormula e
         return (Labeled l e')

    Conn c e1 e2 ->
      do e1' <- importFormula e1
         e2' <- importFormula e2
         return (Conn c e1' e2')

    Not e  ->
      do e' <- importFormula e
         return (Not e')

importTerm :: Expr -> M Simple
importTerm expr =
  case expr of
    Lit {}      -> return expr
    App !_ []   -> return expr
    App !x es   -> compound (App x) es
    Field l e   -> compound (\[a] -> Field l a) [e]
    Record fs   -> compound (\es -> Record (zip (map fst fs) es)) (map snd fs)
    RecordUpdate r fs -> compound (\(s:es) -> RecordUpdate s (zip (map fst fs) es)) (r : map snd fs)
    Cast e t    -> compound (\[a] -> Cast a t) [e]
    If e1 e2 e3 -> compound (\[a,b,c] -> If a b c) [e1,e2,e3]
    Labeled l e -> compound (\[a] -> Labeled l a) [e]

    Match {}    -> error "XXX: importTerm Match"

    Let p e1 e2   ->
      case p of
        PWild   -> importTerm e2

        PVar x  -> do e1' <- importTerm e1
                      let su = Map.singleton x e1'
                      importTerm (apSubst su e2)

        PCon {} -> do e1' <- importTerm e1
                      e2' <- importTerm e2
                      return (Let p e1' e2')

    Quant {}    -> error "Not a term: quant"
    Conn {}     -> error "Not a term: conn"
    Not {}      -> error "Not a term: not"

compound :: ([Simple] -> Shape) -> [Expr] -> M Simple
compound mk es =
  do ts <- mapM importTerm es
     let sh = mk ts
     k <- get
     case Map.lookup sh (sMap k) of
       Just (_,t) -> return t
       Nothing ->
          do let i  = sNext k
                 x  = varName i
                 t  = seq x (App x [])
             set $! S { sMap = Map.insert sh (i,t) (sMap k)
                      , sNext = i + 1 }
             return t

varName :: Int -> Text
varName i = Text.append "cse_" (Text.pack (show i))
