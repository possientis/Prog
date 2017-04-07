-- cannot replace 'where' by 'let' here
doStuff :: Int -> String
doStuff x
  | x < 3     = report "less than three"
  | otherwise = report "normal"
  where
    report y = "the input is " ++ y

{- won't work
doStuff' :: Int -> String
doStuff' x = 
  let report y ="the input is " ++ y in
    | x < 3     = report "less than three" 
    | otherwise = report "normal"

-}
