module  Pretty 
    (   module X 
    ,   Pretty (..)
    )

where
    
import Text.PrettyPrint as X

class Pretty p where
    ppr :: Int -> p -> Doc

    pp  :: p -> Doc
    pp  =  ppr 0
