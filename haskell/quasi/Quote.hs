module  Quote
    (   expr
    )   where


-- import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

expr :: QuasiQuoter
expr =  QuasiQuoter 
     {  quoteExp  = quoteExprExp
     ,  quotePat  = quoteExprPat 
     ,  quoteType = quoteExprType
     ,  quoteDec  = quoteExprDec
     }

quoteExprExp :: String -> TH.ExpQ
quoteExprExp = undefined

quoteExprPat :: String -> TH.PatQ
quoteExprPat = undefined

quoteExprType :: String -> TH.TypeQ
quoteExprType = undefined

quoteExprDec :: String -> TH.Q [TH.Dec]
quoteExprDec  = undefined

