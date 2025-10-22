{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module  Pretty
    (   showExpr
    )   where


import Prelude                  hiding  ((<>))
import Text.PrettyPrint
import Data.Fix

import Op
import Var
import Syntax

showExpr :: Expr -> String
showExpr = render . ppr 0

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
    | op == oNot, [e] <- es = text (show op) <> ppr (p + 1) e  
    | [e1,e2] <-es 
      = parensIf (p > 0) 
      $ ppr (p + 1) e1 
    <+> text (show op) 
    <+> ppr (p + 1) e2
    | otherwise = undefined

pprIf :: Int -> Expr -> Expr -> Expr -> Doc
pprIf p b e1 e2 = parensIf (p > 0) $ 
        text "if" 
    <+> ppr 0 b 
    <+> text "then"
    <+> ppr 0 e1
    <+> text "else"
    <+> ppr 0 e2

pprLam :: Int -> Expr -> Doc
pprLam p e = parensIf (p > 0) $ 
        char '\\'
    <>  hsep (fmap (text . show) (viewVars e))
    <+> text "->"
    <+> ppr 0 (viewBody e)
 
pprApp :: Int -> Expr -> Expr -> Doc
pprApp p e1 e2 = parensIf (p > 0) $ (ppr (p + 1) e1) <+> (ppr (p + 1) e2)

pprRec :: Int -> Var -> Expr -> Doc
pprRec p f e = parensIf (p > 0) $ 
        text "fix" 
    <+> text (show f) 
    <+> text ":="
    <+> ppr 0 e 

pprZero :: Doc
pprZero = text "zero"

pprSuc :: Int -> Expr -> Doc
pprSuc p e = parensIf (p > 0) $ text "suc" <+> ppr (p + 1) e

pprCase :: Int -> Expr -> Expr -> Var -> Expr -> Doc
pprCase p e e1 n e2 = parensIf (p > 0) $
        text "case"
    <+> ppr 0 e
    <+> text "of | zero =>"
    <+> ppr 0 e1  
    <+> text "| suc"
    <+> text (show n)
    <+> text "=>"
    <+> ppr 0 e2

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

