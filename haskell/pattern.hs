-- pattern matching while binding the whole value

contrivedMap :: ([a] -> a -> b) -> [a] -> [b]
contrivedMap f []           = []
contrivedMap f list@(x:xs)  = f list x : contrivedMap f xs 

-- pattern matching with records

data Foo = Bar | Baz { bazNumber :: Int, bazName :: String }

h1 :: Foo -> Int
h1 Bar                                = 0
h1 Baz {bazNumber = 0, bazName=name}  = length name
h1 Baz {}                             = 0

h2 :: Foo -> Int
h2 Bar                = 0
h2 (Baz 0 name)       = length name
h2 (Baz _ _)          = 0


-- even without records
data Foo2 = Bar2 | Baz2 Int

-- no need to change function g with we change implemenation details of Bar2 Baz2
g :: Foo2 -> Bool
g Bar2 {} = True
g Baz2 {} = False


-- pattern matching with list comprehension
catMaybes :: [Maybe a] -> [a]
catMaybes xs = [ x | Just x <- xs ]

-- pattern  matching within do blocks

putFirstChar :: IO ()
putFirstChar = do
  (c:_) <- getLine 
  putStrLn [c]

