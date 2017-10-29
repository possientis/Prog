-- {-# LANGUAGE Safe #-}
{-# LANGUAGE Trustworthy #-} -- why?

import Unsafe.Coerce    -- can't import with Safe extension
import System.IO.Unsafe -- can't import with Safe extension


bad1 :: String
bad1 = unsafePerformIO getLine


bad2 :: a
bad2 = unsafeCoerce 3.14 () 
