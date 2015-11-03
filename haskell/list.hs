data List a = Empty | Cons a (List a) deriving (Show, Read, Eq, Ord)

showList2 :: (Show a) => List a -> String
showList2 Empty = "[]"
showList2 (Cons a b) = show a ++ ":" ++ showList2 b
