{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(x,y,z) 1
#endif

module Language.Why3.Lens
  ( exprPlate
  , _App
  , _Let
  , _If
  , _Match
  , _Conn
  , _Not
  , _Quant
  , _Field
  , _Record
  , _RecordUpdate
  , _Cast
  , _Labeled
  , _And
  , _AsymAnd
  , _Or
  , _AsymOr
  , _Implies
  , _Iff
  , _Goal
  , _Use
  , _Axiom
  , _Lemma
  , _Type
  , _TypeDef
  , _Predicate
  , _PredicateDef
  , _Function
  , _FunctionDef
  , _Import
  , _Export
  , _Integer
  , _Real
  , _Bool
  , _PWild
  , _PVar
  , _PCon
  , _Forall
  , _Exists
  , theoryName
  , theoryDecls
  , tyCaseAltName
  , tyCaseAltLabels
  , tyCaseAltTyParams
  , _TyCon
  , _TyVar
  , _Tuple
  , _TyRecord
  , _Ty
  , _TyCase
  )
  where

import Data.Profunctor
import Data.Text(Text)

import Language.Why3.AST

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif

-- Mirrored definitions

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s
type Prism' s a = forall f p. (Choice p, Applicative f) => a `p` f a -> s `p` f s

_2 :: Lens' (x,a) a
_2 f (x,y) = (,) x <$> f y

prism' :: (a -> s) -> (s -> Maybe a) -> Prism' s a
prism' bt seta =
  dimap (\s -> maybe (Left s) Right (seta s)) (either pure (fmap bt)) . right'

--

exprPlate                      :: Applicative f => (Expr -> f Expr) -> (Expr -> f Expr)
exprPlate f (App n es)          = App n <$> traverse f es
exprPlate f (Let ps e1 e2)      = Let ps <$> f e1 <*> f e2
exprPlate f (If e1 e2 e3)       = If <$> f e1 <*> f e2 <*> f e3
exprPlate f (Match es alts)     = Match <$> traverse f es <*> traverse (_2 f) alts
exprPlate f (Conn c e1 e2)      = Conn c <$> f e1 <*> f e2
exprPlate f (Not e)             = Not <$> f e
exprPlate f (Quant q ts ess e)  = Quant q ts <$> traverse (traverse f) ess <*> f e
exprPlate f (Field n e)         = Field n <$> f e
exprPlate f (Record fs)         = Record <$> traverse (_2 f) fs
exprPlate f (RecordUpdate e fs) = RecordUpdate <$> f e <*> traverse (_2 f) fs
exprPlate f (Cast e t)          = (`Cast` t) <$> f e
exprPlate f (Labeled n e)       = Labeled n <$> f e
exprPlate _ (Lit l)             = pure (Lit l)

-- Expr Prisms

_App                           :: Prism' Expr (Name, [Expr])
_App                            = prism' remitter reviewer
  where
  remitter     (n,es)           = App n es
  reviewer (App n es)           = Just (n,es)
  reviewer _                    = Nothing

_Let                           :: Prism' Expr (Pattern, Expr, Expr)
_Let                            = prism' remitter reviewer
  where
  remitter     (ps,e1,e2)       = Let ps e1 e2
  reviewer (Let ps e1 e2)       = Just (ps,e1,e2)
  reviewer _                    = Nothing

_If                            :: Prism' Expr (Expr, Expr, Expr)
_If                             = prism' remitter reviewer
  where
  remitter    (e1,e2,e3)        = If e1 e2 e3
  reviewer (If e1 e2 e3)        = Just (e1,e2,e3)
  reviewer _                    = Nothing

_Match                         :: Prism' Expr ([Expr], [(Pattern, Expr)])
_Match                          = prism' remitter reviewer
  where
  remitter       (es,alts)      = Match es alts
  reviewer (Match es alts)      = Just (es,alts)
  reviewer _                    = Nothing

_Conn                          :: Prism' Expr (Conn, Expr, Expr)
_Conn                           = prism' remitter reviewer
  where
  remitter      (c,e1,e2)       = Conn c e1 e2
  reviewer (Conn c e1 e2)       = Just (c,e1,e2)
  reviewer _                    = Nothing

_Not                           :: Prism' Expr Expr
_Not                            = prism' remitter reviewer
  where
  remitter                      = Not
  reviewer (Not e)              = Just e
  reviewer _                    = Nothing

_Quant                         :: Prism' Expr (Quant, [(Name,Type)], [[Expr]], Expr)
_Quant                          = prism' remitter reviewer
  where
  remitter       (q,ts,ess,e)   = Quant q ts ess e
  reviewer (Quant q ts ess e)   = Just (q,ts,ess,e)
  reviewer _                    = Nothing

_Field                         :: Prism' Expr (Name, Expr)
_Field                          = prism' remitter reviewer
  where
  remitter       (n,e)          = Field n e
  reviewer (Field n e)          = Just (n,e)
  reviewer _                    = Nothing

_Record                        :: Prism' Expr [(Name,Expr)]
_Record                         = prism' remitter reviewer
  where
  remitter                      = Record
  reviewer (Record fs)          = Just fs
  reviewer _                    = Nothing

_RecordUpdate                  :: Prism' Expr (Expr, [(Name,Expr)])
_RecordUpdate                   = prism' remitter reviewer
  where
  remitter (e,fs)               = RecordUpdate e fs
  reviewer (RecordUpdate e fs)  = Just (e,fs)
  reviewer _                    = Nothing

_Cast                          :: Prism' Expr (Expr, Type)
_Cast                           = prism' remitter reviewer
  where
  remitter      (e,t)           = Cast e t
  reviewer (Cast e t)           = Just (e,t)
  reviewer _                    = Nothing

_Labeled                       :: Prism' Expr (Name,Expr)
_Labeled                        = prism' remitter reviewer
  where
  remitter         (n,e)        = Labeled n e
  reviewer (Labeled n e)        = Just (n,e)
  reviewer _                    = Nothing

-- Conn Prisms

_And                           :: Prism' Conn ()
_And                            = prism' remitter reviewer
  where
  remitter _                    = And
  reviewer And                  = Just ()
  reviewer _                    = Nothing

_AsymAnd                       :: Prism' Conn ()
_AsymAnd                        = prism' remitter reviewer
  where
  remitter _                    = AsymAnd
  reviewer AsymAnd              = Just ()
  reviewer _                    = Nothing

_Or                            :: Prism' Conn ()
_Or                             = prism' remitter reviewer
  where
  remitter _                    = Or
  reviewer Or                   = Just ()
  reviewer _                    = Nothing

_AsymOr                        :: Prism' Conn ()
_AsymOr                         = prism' remitter reviewer
  where
  remitter _                    = AsymOr
  reviewer AsymOr               = Just ()
  reviewer _                    = Nothing

_Implies                       :: Prism' Conn ()
_Implies                        = prism' remitter reviewer
  where
  remitter _                    = Implies
  reviewer AsymOr               = Just ()
  reviewer _                    = Nothing

_Iff                           :: Prism' Conn ()
_Iff                            = prism' remitter reviewer
  where
  remitter _                    = Iff
  reviewer Iff                  = Just ()
  reviewer _                    = Nothing

-- Decl Prisms

_Goal                          :: Prism' Decl (Name,Expr)
_Goal                           = prism' remitter reviewer
  where
  remitter      (n,e)           = Goal n e
  reviewer (Goal n e)           = Just (n,e)
  reviewer _                    = Nothing

_Use                           :: Prism' Decl (Maybe ImpExp, Name, Maybe Name)
_Use                            = prism' remitter reviewer
  where
  remitter     (x,y,z)          = Use x y z
  reviewer (Use x y z)          = Just (x,y,z)
  reviewer _                    = Nothing

_Axiom                         :: Prism' Decl (Name,Expr)
_Axiom                          = prism' remitter reviewer
  where
  remitter       (x,y)          = Axiom x y
  reviewer (Axiom x y)          = Just (x,y)
  reviewer _                    = Nothing

_Lemma                         :: Prism' Decl (Name,Expr)
_Lemma                          = prism' remitter reviewer
  where
  remitter       (x,y)          = Lemma x y
  reviewer (Lemma x y)          = Just (x,y)
  reviewer _                    = Nothing

_Type                          :: Prism' Decl (Name, [Text], [(Name, [Text])])
_Type                           = prism' remitter reviewer
  where
  remitter      (x,y,z)         = Type x y z
  reviewer (Type x y z)         = Just (x,y,z)
  reviewer _                    = Nothing

_TypeDef                       :: Prism' Decl (Name, [Text], [(Name, [Text])], TypeDef)
_TypeDef                        = prism' remitter reviewer
  where
  remitter         (x,y,z,w)    = TypeDef x y z w
  reviewer (TypeDef x y z w)    = Just (x,y,z,w)
  reviewer _                    = Nothing

_Predicate                     :: Prism' Decl (Name, [Text], [Type])
_Predicate                      = prism' remitter reviewer
  where
  remitter           (x,y,z)    = Predicate x y z
  reviewer (Predicate x y z)    = Just (x,y,z)
  reviewer _                    = Nothing

_PredicateDef                  :: Prism' Decl (Name, [Text], [(Maybe Name, Type)], Expr)
_PredicateDef                   = prism' remitter reviewer
  where
  remitter              (x,y,z,w) = PredicateDef x y z w
  reviewer (PredicateDef x y z w) = Just (x,y,z,w)
  reviewer _                      = Nothing

_Function                      :: Prism' Decl (Name, [Text], [Type], Type)
_Function                       = prism' remitter reviewer
  where
  remitter          (x,y,z,w)   = Function x y z w
  reviewer (Function x y z w)   = Just (x,y,z,w)
  reviewer _                    = Nothing

_FunctionDef                   :: Prism' Decl (Name, [Text], [(Maybe Name, Type)], Type, Expr)
_FunctionDef                    = prism' remitter reviewer
  where
  remitter             (x,y,z,w,v) = FunctionDef x y z w v
  reviewer (FunctionDef x y z w v) = Just      (x,y,z,w,v)
  reviewer _                       = Nothing

-- ImpExp Prisms

_Import                        :: Prism' ImpExp ()
_Import                         = prism' remitter reviewer
  where
  remitter _                    = Import
  reviewer Import               = Just ()
  reviewer _                    = Nothing

_Export                        :: Prism' ImpExp ()
_Export                         = prism' remitter reviewer
  where
  remitter _                    = Export
  reviewer Export               = Just ()
  reviewer _                    = Nothing

-- Literal Prisms

_Integer                       :: Prism' Literal Integer
_Integer                        = prism' remitter reviewer
  where
  remitter                      = Integer
  reviewer (Integer x)          = Just x
  reviewer _                    = Nothing

_Real                          :: Prism' Literal Text
_Real                           = prism' remitter reviewer
  where
  remitter                      = Real
  reviewer (Real x)             = Just x
  reviewer _                    = Nothing

_Bool                          :: Prism' Literal Bool
_Bool                           = prism' remitter reviewer
  where
  remitter                      = Bool
  reviewer (Bool x)             = Just x
  reviewer _                    = Nothing

-- Pattern Prisms

_PWild                         :: Prism' Pattern ()
_PWild                          = prism' remitter reviewer
  where
  remitter _                    = PWild
  reviewer PWild                = Just ()
  reviewer _                    = Nothing

_PVar                          :: Prism' Pattern Name
_PVar                           = prism' remitter reviewer
  where
  remitter                      = PVar
  reviewer (PVar x)             = Just x
  reviewer _                    = Nothing

_PCon                          :: Prism' Pattern (Name, [Pattern])
_PCon                           = prism' remitter reviewer
  where
  remitter      (x,y)           = PCon x y
  reviewer (PCon x y)           = Just (x,y)
  reviewer _                    = Nothing

-- Quant Prisms

_Forall                        :: Prism' Quant ()
_Forall                         = prism' remitter reviewer
  where
  remitter _                    = Forall
  reviewer Forall               = Just ()
  reviewer _                    = Nothing

_Exists                        :: Prism' Quant ()
_Exists                         = prism' remitter reviewer
  where
  remitter _                    = Exists
  reviewer Exists               = Just ()
  reviewer _                    = Nothing

-- Theory Lenses

theoryName                     :: Lens' Theory Name
theoryName f (Theory n ds)      = (`Theory` ds) <$> f n

theoryDecls                    :: Lens' Theory [Decl]
theoryDecls f (Theory n ds)     = Theory n <$> f ds

-- TyCaseAlt Lenses

tyCaseAltName                          :: Lens' TyCaseAlt Name
tyCaseAltName f (TyCaseAlt x y z)       = fmap (\x' -> TyCaseAlt x' y z) (f x)

tyCaseAltLabels                        :: Lens' TyCaseAlt [Text]
tyCaseAltLabels f (TyCaseAlt x y z)     = fmap (\y' -> TyCaseAlt x y' z) (f y)

tyCaseAltTyParams                      :: Lens' TyCaseAlt [(Maybe Name, Type)]
tyCaseAltTyParams f (TyCaseAlt x y z)   = TyCaseAlt x y <$> f z

-- Type Prisms

_TyCon                         :: Prism' Type (Name,[Type])
_TyCon                          = prism' remitter reviewer
  where
  remitter       (x,y)          = TyCon x y
  reviewer (TyCon x y)          = Just (x,y)
  reviewer _                    = Nothing

_TyVar                         :: Prism' Type Name
_TyVar                          = prism' remitter reviewer
  where
  remitter                      = TyVar
  reviewer (TyVar x)            = Just x
  reviewer _                    = Nothing

_Tuple                         :: Prism' Type [Type]
_Tuple                          = prism' remitter reviewer
  where
  remitter                      = Tuple
  reviewer (Tuple x)            = Just x
  reviewer _                    = Nothing

-- TypeDef Prisms

_TyRecord                      :: Prism' TypeDef [(Name,Type)]
_TyRecord                       = prism' remitter reviewer
  where
  remitter                      = TyRecord
  reviewer (TyRecord x)         = Just x
  reviewer _                    = Nothing

_Ty                            :: Prism' TypeDef Type
_Ty                             = prism' remitter reviewer
  where
  remitter                      = Ty
  reviewer (Ty x)               = Just x
  reviewer _                    = Nothing

_TyCase                        :: Prism' TypeDef [TyCaseAlt]
_TyCase                         = prism' remitter reviewer
  where
  remitter                      = TyCase
  reviewer (TyCase x)           = Just x
  reviewer _                    = Nothing
