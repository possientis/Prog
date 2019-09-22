{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ScopedTypeVariables    #-}

import Data.Kind
import Data.Proxy
import GHC.TypeLits

data Format
    = Number Format
    | Str    Format
    | Chr    Format
    | Dbl    Format
    | Lit    Symbol Format
    | End


data SFormat
    = SNumber SFormat
    | SStr    SFormat
    | SChr    SFormat
    | SDbl    SFormat
    | SLit    String SFormat
    | SEnd

class KnownFormat (t :: Format) where
    formatValue :: Proxy t -> SFormat

instance KnownFormat fmt => KnownFormat ('Number fmt) where
    formatValue _ = SNumber (formatValue (Proxy :: Proxy fmt))

instance KnownFormat fmt => KnownFormat ('Str fmt) where
    formatValue _ = SStr (formatValue (Proxy :: Proxy fmt)) 

instance KnownFormat fmt => KnownFormat ('Chr fmt) where
    formatValue _ = SChr (formatValue (Proxy :: Proxy fmt))

instance KnownFormat fmt => KnownFormat ('Dbl fmt) where
    formatValue _ = SDbl (formatValue (Proxy :: Proxy fmt))

instance (KnownSymbol str, KnownFormat fmt) => KnownFormat ('Lit str fmt) where
    formatValue _ = SLit 
        (symbolVal (Proxy :: Proxy str)) 
        (formatValue (Proxy :: Proxy fmt))

instance KnownFormat 'End where
    formatValue _ = SEnd


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

instance HasPrintf (t :: Format) => HasPrintf ('Number t) where
    printfFmt _ acc = \i -> printfFmt (Proxy :: Proxy t) (acc ++ show i)

instance HasPrintf (t :: Format) => HasPrintf ('Str t) where
    printfFmt _ acc = \s -> printfFmt (Proxy :: Proxy t) (acc ++ s)

instance HasPrintf (t :: Format) => HasPrintf ('Chr t) where
    printfFmt _ acc = \c -> printfFmt (Proxy :: Proxy t) (acc ++ show c)

instance HasPrintf (t :: Format) => HasPrintf ('Dbl t) where
    printfFmt _ acc = \d -> printfFmt (Proxy :: Proxy t) (acc ++ show d)

instance (KnownSymbol str, HasPrintf (t :: Format)) => 
    HasPrintf ('Lit str t) where
        printfFmt (Proxy :: Proxy ('Lit str t)) acc = printfFmt 
            (Proxy :: Proxy t) 
            (acc ++ symbolVal (Proxy :: Proxy str))


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



