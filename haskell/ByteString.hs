{-# LANGUAGE OverloadedStrings #-}

import qualified Data.ByteString as S
import qualified Data.ByteString.Char8 as S8
import Data.Word8

{- fails 
bstr1 :: S.ByteString
bstr1 = S.pack ("foo" :: String)
-}

bstr2 :: S.ByteString
bstr2 = "bar"
