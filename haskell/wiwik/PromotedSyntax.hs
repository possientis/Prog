{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

import GHC.Types

-- ghci -XTypeOperators -XDataKinds

{-
 -
 - :k 1
 - 1 :: Nat
 -
 - :k "foo"
 - "foo" :: Symbol 
 -
 - :k [1,2,3]
 - [1,2,3] :: [Nat]
 -
 - :k [Int,Bool,Char]
 - [Int,Bool,Char] :: [*]
 -
 - :k Just [Int,Bool,Char]
 - Just [Int,Bool,Char] :: Maybe [*]
 -
 - :k '("a",Int)    -- note the quote ' character
 - '("a",Int) :: (Symbol, *)
 -
 - :k [ '("a",Int), '("b",Bool) ]
 - ['("a",Int), '("b",Bool)] :: [(Symbol,*)]
 -
 -}




