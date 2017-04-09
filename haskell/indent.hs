{-
  Code which is part of some expression should be indented 
  further in than the beginning of that expression.
  necessary condition, but not sufficient.
-}


main = let 
        x = 1
        y = 3
  in putStrLn $ show (x + y) -- did you say necessary?

main' = let { x = 1; y =3; } in putStrLn $ show (x + y)
