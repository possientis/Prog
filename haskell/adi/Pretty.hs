{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module  Pretty
    (   Pretty  (..)
    )   where


import Text.PrettyPrint
import Data.Functor.Foldable

import Var
import Syntax

class Pretty p where 
    ppr :: Int -> p -> Doc
    pp  :: p -> Doc
    pp = ppr 0

viewVars :: Expr -> [Var]
viewVars = \case
    Fix (ELam x e) ->  x : viewVars e
    _              -> [] 

viewBody :: Expr -> Expr
viewBody = \case
    Fix (ELam _ e) -> viewBody e
    x              -> x 

parensIf :: Bool -> Doc -> Doc
parensIf = \case
    True    -> parens
    False   -> id

instance Pretty Expr where
    ppr p = \case
        Fix (ENum n)            -> pprNum n 
        Fix (EBool b)           -> pprBool b
        Fix (EVar x)            -> pprVar x
        Fix (EOp _op _vs)       -> undefined
        Fix (EIf _b _e1 _e2)    -> undefined
        Fix (ELam _x _e)        -> undefined
        Fix (EApp f e)          -> parensIf (p>0) $ (ppr (p+1) f) <+> (ppr (p+1) e)
        _                       -> undefined

pprNum :: Integer -> Doc
pprNum = text . show

pprBool :: Bool -> Doc
pprBool = text . show

pprVar :: Var -> Doc
pprVar = text . show



