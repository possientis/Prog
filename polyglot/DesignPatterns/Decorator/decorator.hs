-- Decorator Design Pattern

class Pizza a where
  description :: a -> String
  cost        :: a -> Double

data PlainPizza           = PlainPizza
data WithExtraCheese a    = AddCheese a
data WithExtraOlives a    = AddOlives a
data WithExtraAnchovies a = AddAnchovies a


instance Pizza PlainPizza where
  description _ = "Plain pizza"
  cost        _ = 3.0

instance (Pizza a) => Pizza (WithExtraCheese a) where
  description (AddCheese x) = description x ++ " + extra cheese"
  cost        (AddCheese x) = cost x + 0.5

instance (Pizza a) => Pizza (WithExtraOlives a) where
  description (AddOlives x) = description x ++ " + extra olives"
  cost        (AddOlives x) = cost x + 0.7

instance (Pizza a) => Pizza (WithExtraAnchovies a) where
  description (AddAnchovies x) = description x ++ " + extra anchovies"
  cost        (AddAnchovies x) = cost x + 0.8



main = do
  let plainPizza  = PlainPizza
  let nicePizza   = AddCheese PlainPizza
  let superPizza  = AddOlives (AddCheese PlainPizza)
  let ultraPizza  = AddAnchovies (AddOlives (AddCheese PlainPizza))
  
  putStrLn $  "Plain Pizza: "   ++
              "\tCost: "        ++ show (cost plainPizza)
          ++  "\tDescription: " ++ description plainPizza 

  putStrLn $  "Nice Pizza: "    ++
              "\tCost: "        ++ show (cost nicePizza)
          ++  "\tDescription: " ++ description nicePizza 

  putStrLn $  "Super Pizza: "   ++
              "\tCost: "        ++ show (cost superPizza)
          ++  "\tDescription: " ++ description superPizza 

  putStrLn $  "Ultra Pizza: "    ++
              "\tCost: "        ++ show (cost ultraPizza)
          ++  "\tDescription: " ++ description ultraPizza 


