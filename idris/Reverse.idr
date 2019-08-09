myReverse : List a -> List a
myReverse xs = go xs [] where
  go : List a -> List a -> List a
  go [] ys        = ys
  go (x :: xs) ys = go xs (x :: ys)


main : IO ()
main = do
  putStrLn $ show $ myReverse [1,2,3,4,5,6,7,8,9,0]

