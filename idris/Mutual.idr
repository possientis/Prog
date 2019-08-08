mutual
  isEven : Nat -> Bool
  isEven Z     = True
  isEven (S k) = isOdd k

  isOdd  : Nat -> Bool
  isOdd Z     = False
  isOdd (S k) = isEven k


main : IO ()
main = do
  putStrLn $ show (isEven 34)
  putStrLn $ show (isOdd  67)
