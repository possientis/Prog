{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}

import Data.Kind
import Data.Proxy

data Format
    = Number Format
    | Str    Format
    | Chr    Format
    | Dbl    Format
    | Lit    String Format
    | End


type family PrintfType (t :: Format) :: Type where
    PrintfType ('Number fmt) = Int      -> PrintfType fmt
    PrintfType ('Str    fmt) = String   -> PrintfType fmt
    PrintfType ('Chr    fmt) = Char     -> PrintfType fmt
    PrintfType ('Dbl    fmt) = Double   -> PrintfType fmt
    PrintfType ('Lit _  fmt) =             PrintfType fmt
    PrintfType 'End          =             String

class HasPrintf (t :: Format) where
    printfFmt :: Proxy t -> String -> PrintfType t

instance HasPrintf 'End where
    printfFmt _ acc = acc


{-
class HasPrintf (t :: Format) where
    type PrintfType t :: Type 
    printfFmt :: Proxy t -> String -> PrintfType t


instance HasPrintf 'End where
    type PrintfType 'End = String

instance HasPrintf fmt => HasPrintf ('Number fmt) where
    type PrintfType ('Number fmt) = Int -> PrintfType fmt

instance HasPrintf fmt => HasPrintf ('Str fmt) where
    type PrintfType ('Str fmt) = String -> PrintfType fmt

instance HasPrintf fmt => HasPrintf ('Chr fmt) where
    type PrintfType ('Chr fmt) = Char -> PrintfType fmt

instance HasPrintf fmt => HasPrintf ('Dbl fmt) where
    type PrintfType ('Dbl fmt) = Double -> PrintfType fmt

instance HasPrintf fmt => HasPrintf ('Lit s fmt) where
    type PrintfType ('Lit s fmt) = PrintfType fmt
-}



