{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-} -- why?

import Data.Text

-- string literals of type 'Text' by default
-- need OverloadedStrings to take effect
default (Text)


example = "foo"


myTStr1 :: Text
myTStr1 = pack ("foo" :: String)


myTStr2 :: Text
myTStr2 = "bar"
