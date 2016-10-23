median :: (Integral a, Fractional b) => [a] -> b
median [] = error "Empty List" 
median xs 
   | odd l     = realToFrac $ ys !! h
   | otherwise = realToFrac (ys !! h + ys !! (h-1)) / 2
   where  l  = length xs
        h  = l `div` 2
        ys = sort xs

quartiles :: [Int] -> (Double, Double, Double)
quartiles xs
   | length xs < 4 = error "List must contain more than 3 elements"
   | otherwise     = (first_q, second_q, third_q)
   where lista  = sort xs
         first  = median $ fst $ splitAt ( div (length lista 2)) lista
         second = median lista
         third  = median $ snd $ splitAt ( div (length lista 2)+ 1 ) lista
