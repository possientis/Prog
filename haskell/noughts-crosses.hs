data Board = Board

nextConfigs :: Board -> [Board]
nextConfigs = undefined

tick :: [Board] -> [Board]
tick bds = concatMap nextConfigs bds

thirdConfigs''' :: Board -> [Board]
thirdConfigs''' bd = tick $ tick $ tick [bd]

--using monad structure for [a]
thirdConfigs'' :: Board -> [Board]
thirdConfigs'' bd = return bd >>= nextConfigs >>= nextConfigs >>= nextConfigs


thirdConfigs' :: Board -> [Board]
thirdConfigs' bd = do
  bd0 <-  return bd         -- initial config
  bd1 <-  nextConfigs bd0   -- After one turn 
  bd2 <-  nextConfigs bd1   -- After two turns
  bd3 <-  nextConfigs bd2   -- After three turns
  return bd3


thirdConfigs :: Board -> [Board]
thirdConfigs bd = [ bd3 | bd1 <- nextConfigs bd
                        , bd2 <- nextConfigs bd1
                        , bd3 <- nextConfigs bd2 ]




