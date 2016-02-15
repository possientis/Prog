palindrome []     = []
palindrome (x:xs) = x:((palindrome xs) ++ [x])

isPalindrome []   = True
isPalindrome [x]  = False 
isPalindrome (x:xs) 
  | x == last xs  = isPalindrome ys 
  | otherwise     = False 
  where ys = (take (length xs - 1) xs)
