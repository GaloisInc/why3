-- | Functions for working with names.
module Language.Why3.Names
  ( countUses
  , rename
  , apSubst
  , freeNames
  ) where

import Language.Why3.AST

import           Data.List (foldl')
import           Data.Monoid ((<>))

import           Data.Map  ( Map )
import qualified Data.Map as Map
import qualified Data.Map.Strict as MapStrict

import           Data.Set  ( Set )
import qualified Data.Set as Set

import Data.List (mapAccumL)

import qualified Data.Text as Text

-- | Find free names in an expression
freeNames :: Expr -> Set Name
freeNames = Map.keysSet . countUses

-- | Count the uses of free names in an expression.
countUses :: Expr -> Map Name Int
countUses = getCount . go
  where
  go sh =
    case sh of
      Lit _             -> mempty
      App x es          -> countOne x <> foldMap go es
      If e1 e2 e3       -> go e1 <> go e2 <> go e3
      Conn _ e1 e2      -> go e1 <> go e2
      Not e             -> go e
      Field _ e         -> go e
      Record es         -> foldMap (go . snd) es
      RecordUpdate e es -> go e <> foldMap (go . snd) es
      Cast e _          -> go e
      Labeled _ e       -> go e

      -- cases with shadowing
      Quant _ xs _ e -> forgetMany (map fst xs) (go e)
      Match es as    -> foldMap go es <> foldMap alt as
          where alt (p,e) = forgetMany (Set.toList (patDefines p)) (go e)
      Let p e1 e2    -> go e1 <> forgetMany (Set.toList (patDefines p)) (go e2)

countOne :: k -> Count k
countOne k = Count (Map.singleton k 1)

forget :: Ord k => k -> Count k -> Count k
forget k (Count m) = Count (Map.delete k m)

forgetMany :: Ord k => [k] -> Count k -> Count k
forgetMany ks count = foldl' (flip forget) count ks

newtype Count k = Count { getCount :: Map k Int }

instance Ord k => Monoid (Count k) where
  mempty = Count Map.empty
  mappend (Count x) (Count y) = Count (MapStrict.unionWith (+) x y)


-- | Rename an expression to avoid all shadowing.  The input parameters is
-- a set of names that are already in scope and, therefore, should be renamed.
rename :: Set Name -> Expr -> Expr
rename used0 = go (Map.fromList [ (x,x) | x <- Set.toList used0 ])
  where
  variants       :: Name -> [Name]
  variants x      = x : [ Text.append x (Text.pack (show n))
                                          | n <- [ (1 :: Integer) .. ] ]

  pickName :: Map Name Name -> Name -> (Map Name Name, Name)
  pickName used x = let Just y = find (`Map.notMember` used) (variants x)
                    in (Map.insert x y used, y)

  getName :: Map Name Name -> Name -> Name
  getName nm x = Map.findWithDefault x x nm

  go :: Map Name Name -> Expr -> Expr
  go nm expr =
    case expr of
      Lit _               -> expr

      App x es            -> App (getName nm x) (map (go nm) es)

      Let p e1 e2         -> let (nm1,p1) = renP nm p
                             in Let p1 (go nm e1) (go nm1 e2)

      Quant q xs trs e    -> let (nm1, ys) = mapAccumL renQ nm xs
                             in Quant q ys (map (map (go nm1)) trs) (go nm1 e)
        where renQ nm1 (x,t) = let (nm2, y) = pickName nm1 x
                               in (nm2, (y,t))

      If e1 e2 e3         -> If (go nm e1) (go nm e2) (go nm e3)
      Match es alts       -> Match (map (go nm) es)
                           $ map (renAlt nm) alts

      Conn c e1 e2        -> Conn c (go nm e1) (go nm e2)
      Not e               -> Not (go nm e)
      Field l e           -> Field l (go nm e)
      Record fs           -> Record [ (x, go nm e) | (x,e) <- fs ]
      RecordUpdate r fs   -> RecordUpdate (go nm r) [ (x, go nm e) | (x,e) <- fs ]

      Labeled l e         -> Labeled l (go nm e)
      Cast e t            -> Cast (go nm e) t

  renAlt nm (p,e) = let (nm1,p1) = renP nm p
                    in (p1, go nm1 e)

  renP nm pat =
    case pat of
      PWild     -> (nm, PWild)
      PVar x    -> let (nm1, y) = pickName nm x
                in (nm1, PVar y)
      PCon c ps -> let (nm1, ps1) = mapAccumL renP nm ps
                   in (nm1, PCon c ps1)


-- | Apply a substitution to an exprssion.
-- WARNING: This assumes that no capturing of variables will occur.
-- This function treats names without arguments applied to them as the
-- variables elligible for substitution.
apSubst :: Map Name Expr -> Expr -> Expr
apSubst = go
  where
  go env expr =
    case expr of
      Lit _               -> expr

      App x []            -> Map.findWithDefault expr x env
      App x es            -> App x (map (go env) es)

      Match es alts -> Match (map (go env) es) $ map inAlt alts
        where
        -- Here we assume no capture
        inAlt (p,e) =
          let defs = patDefines p
              env1 = Map.filterWithKey (\x _ -> not (x `Set.member` defs)) env
          in (p, go env1 e)

      -- Here we assume no captrue
      Let p e1 e2         -> Let p (go env e1) (go env1 e2)
        where
        env1 = let defs = patDefines p
               in Map.filterWithKey (\x _ -> not (x `Set.member` defs)) env

      -- Here we assume no captrue
      Quant q as trs e ->
        let env1 = foldr (Map.delete . fst) env as
        in Quant q as (map (map (go env1)) trs) (go env1 e)


      If e1 e2 e3         -> If (go env e1) (go env e2) (go env e3)
      Conn c e1 e2        -> Conn c (go env e1) (go env e2)
      Not e               -> Not (go env e)
      Field l e           -> Field l (go env e)
      Record fs           -> Record [ (x, go env e) | (x,e) <- fs ]
      RecordUpdate r fs   -> RecordUpdate (go env r) [ (x, go env e) | (x,e) <- fs ]

      Cast e t            -> Cast (go env e) t
      Labeled l e         -> Labeled l (go env e)

patDefines :: Pattern -> Set Name
patDefines pat =
  case pat of
    PWild     -> Set.empty
    PVar x    -> Set.singleton x
    PCon _ ps -> Set.unions (map patDefines ps)
