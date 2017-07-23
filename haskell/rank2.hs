{-# LANGUAGE Rank2Types #-}

data Number = FloatVal  Float 
            | IntVal    Int
            deriving (Show)


applyFn :: AddOp -> Number -> Number -> Either String Number
applyFn f   (IntVal n)  (IntVal m)  = Right $ IntVal    $ f n m  
applyFn f   (FloatVal x)(FloatVal y)= Right $ FloatVal  $ f x y
applyFn _   _           _           = Left "Mismatch"        


main :: IO ()
main = do
    putStrLn $ show $ applyFn (+) (IntVal 3) (IntVal 4)
    putStrLn $ show $ applyFn (+) (FloatVal 2.5) (FloatVal 4.5)
    putStrLn $ show $ applyFn (+) (IntVal 3) (FloatVal 2.3)


