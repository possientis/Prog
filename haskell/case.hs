x = Just 6

y = case x of
  Nothing     -> 0
  Just value  -> value
