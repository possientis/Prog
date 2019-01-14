{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module  Lambda
    (
    )   where

import Pretty

type Name = String

instance Pretty Name where
    ppr p s = text s

data Lit 
    = LInt Int
    | LBool Bool

data Expr
    = Var Name
    | App Expr Expr
    | Lam Name Expr
    | Fix Expr
    | Let Name Expr Expr
    | LetRec Name Expr Expr
    | Lit Lit


viewVars :: Expr -> [Name]
viewVars (Lam n a) = n : viewVars a
viewVars _         = []

viewBody :: Expr -> Expr
viewBody (Lam _ a) = a
viewBody x         = x

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id


instance Pretty Expr where
    ppr p e = case e of
        Lit (LInt a)  -> text (show a)
        Lit (LBool b) -> text (show b)
        Var x         -> text x
        App a b       -> parensIf (p>0) $ (ppr (p+1) a) <+> (ppr p b) 
        Lam x a       -> parensIf (p>0) $
            char '\\'
         <>  hsep (map pp (viewVars e))
         <+> text "->"
         <+> ppr (p+1) (viewBody e)

ppexpr :: Expr -> String
ppexpr = render . ppr 0


test :: String
test = ppexpr (Lam "x" (Lam "y" (App (Var "x") (Var "y"))))

main :: IO ()
main = putStrLn test
