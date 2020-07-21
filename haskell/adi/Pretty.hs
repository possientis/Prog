{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module  Pretty
    (   ppr     -- remove
    )   where


import Prelude                  hiding  ((<>))
import Text.PrettyPrint
import Data.Functor.Foldable

import Op
import Var
import Syntax

ppr :: Int -> Expr -> Doc
ppr p = \case
    Fix (ENum n)            -> pprNum n 
    Fix (EBool b)           -> pprBool b
    Fix (EVar x)            -> pprVar x
    Fix (EOp op vs)         -> pprOp p op vs
    Fix (EIf b e1 e2)       -> pprIf p b e1 e2
    e@(Fix (ELam _ _))      -> pprLam p e
    Fix (EApp e1 e2)        -> pprApp p e1 e2
    Fix (ERec f e)          -> pprRec p f e
    Fix (EZero)             -> pprZero
    Fix (ESuc e)            -> pprSuc p e
    Fix (ECase e e1 n e2)   -> pprCase p e e1 n e2

pprNum :: Integer -> Doc
pprNum = text . show

pprBool :: Bool -> Doc
pprBool = text . show

pprVar :: Var -> Doc
pprVar = text . show

pprOp :: Int -> Op -> [Expr] -> Doc
pprOp p op es
    | op == oNot    = let [e] = es in text (show op) <+> ppr (p + 1) e  
    | otherwise     = parensIf (p > 0) $ let [e1,e2] = es in
        ppr (p + 1) e1 
    <+> text (show op) 
    <+> ppr (p + 1) e2

pprIf :: Int -> Expr -> Expr -> Expr -> Doc
pprIf p b e1 e2 = parensIf (p > 0) $ 
        text "if" 
    <+> ppr (p + 1) b 
    <+> text "then"
    <+> ppr (p + 1) e1
    <+> text "else"
    <+> ppr (p + 1) e2

pprLam :: Int -> Expr -> Doc
pprLam p e = parensIf (p > 0) $ 
        char '\\' 
    <>  hsep (fmap (text . show) (viewVars e))
    <+> text "->"
    <+> ppr (p + 1) (viewBody e)
 
pprApp :: Int -> Expr -> Expr -> Doc
pprApp p e1 e2 = parensIf (p > 0) $ (ppr (p + 1) e1) <+> (ppr (p + 1) e2)

pprRec :: Int -> Var -> Expr -> Doc
pprRec p f e = parensIf (p > 0) $ 
        text "fix" 
    <+> text (show f) 
    <+> text ":="
    <+> ppr (p + 1) e 

pprZero :: Doc
pprZero = text "zero"

pprSuc :: Int -> Expr -> Doc
pprSuc p e = parensIf (p > 0) $ text "suc" <+> ppr (p + 1) e

pprCase :: Int -> Expr -> Expr -> Var -> Expr -> Doc
pprCase p e e1 n e2 = parensIf (p > 0) $
        text "case"
    <+> ppr (p + 1) e
    <+> text "of | zero =>"
    <+> ppr (p + 1) e1  
    <+> text "| suc"
    <+> text (show n)
    <+> text "=>"
    <+> ppr (p + 1) e2

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


