module  Quote
    (   expr
    )   where


import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

import Expr
import Parse

expr :: QuasiQuoter
expr =  QuasiQuoter 
     {  quoteExp  = quoteExprExp
     ,  quotePat  = quoteExprPat 
     ,  quoteType = quoteExprType
     ,  quoteDec  = quoteExprDec
     }

quoteExprExp :: String -> TH.ExpQ
quoteExprExp s = do
    loc <- TH.location
    let pos = ( TH.loc_filename loc
              , fst (TH.loc_start loc)
              , snd (TH.loc_start loc)
              )
    e <- parseExpr pos s
    dataToExpQ (const Nothing `extQ` antiExprExp) e

antiExprExp :: Expr -> Maybe (TH.Q TH.Exp)
antiExprExp (EAntiInt s) = Just $ TH.appE (TH.conE (TH.mkName "ELitInt"))
                                          (TH.varE (TH.mkName s))
antiExprExp (EAntiExp s) = Just $ TH.varE (TH.mkName s)
antiExprExp _            = Nothing

quoteExprPat :: String -> TH.PatQ
quoteExprPat s = do
    loc <- TH.location
    let pos = ( TH.loc_filename loc
              , fst (TH.loc_start loc)
              , snd (TH.loc_start loc)
              )
    e <- parseExpr pos s
    dataToPatQ (const Nothing `extQ` antiExprPat) e

antiExprPat :: Expr -> Maybe (TH.Q TH.Pat)
antiExprPat (EAntiInt s) = Just $ TH.conP (TH.mkName "ELitInt")
                                          [TH.varP (TH.mkName s)]
antiExprPat (EAntiExp s) = Just $ TH.varP (TH.mkName s)
antiExprPat _            = Nothing 

        
quoteExprType :: String -> TH.TypeQ
quoteExprType = undefined

quoteExprDec :: String -> TH.Q [TH.Dec]
quoteExprDec  = undefined

