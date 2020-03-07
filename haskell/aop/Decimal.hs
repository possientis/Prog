{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}

module  Decimal
    (   Digit   (..) 
    ,   wholeDigits
    ,   fracDigits
    ,   rep1
    ,   eval
    )   where

import List

import Control.Lens

data Digit = D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9

instance Show Digit where
    show = \case
        D0 -> "0"
        D1 -> "1"
        D2 -> "2"
        D3 -> "3"
        D4 -> "4"
        D5 -> "5"
        D6 -> "6"
        D7 -> "7"
        D8 -> "8"
        D9 -> "9"

evalD :: Digit -> Double
evalD = read . show 

data DecimalRep = DecimalRep
    { _wholeDigits :: ListS Digit
    , _fracDigits  :: ListC Digit
    } deriving (Show)

makeLenses ''DecimalRep

rep1 :: DecimalRep
rep1 =  DecimalRep
    { _wholeDigits = fromListS [D1,D2,D3,D4]
    , _fracDigits  = fromListC [D5,D6,D7,D8,D9]
    }

eval :: DecimalRep -> Double
eval r = w + f where
    w = foldS 0 (\x y -> x * 10 + y)  $ fmap evalD $ r ^. wholeDigits
    f = foldC 0 (\x y -> (x + y)/10 ) $ fmap evalD $ r ^. fracDigits 
