{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-} -- why?

import Data.Text

-- string literals of type 'Text' by default
-- need OverloadedStrings to take effect
default (Text)


example = "foo"
