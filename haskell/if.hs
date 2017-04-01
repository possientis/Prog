-- if then else
if_func1 :: Bool -> a -> a -> a
if_func1 cond x y = 
  if cond then x else y

-- pattern matching
if_func2 :: Bool -> a -> a -> a
if_func2 True x _   = x
if_func2 False _ y  = y

-- guards
if_func3 :: Bool -> a -> a -> a
if_func3 cond x y
  | cond == True  = x
  | cond == False = y

-- case expression
if_func4 :: Bool -> a -> a -> a
if_func4 cond y x =
  case cond of
    True  -> x
    False -> y
