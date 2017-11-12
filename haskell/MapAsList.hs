{-# LANGUAGE TypeFamilies, OverloadedLists #-}

import Data.Map
--import GHC.Exts (IsList (..))


example1 :: Map String Int
example1 = [("a",1),("b",2)] -- need OverloadedLists
