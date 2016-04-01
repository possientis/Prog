import Set
import qualified Data.Map as Map

data HashManager = HashManager {
  nextHash      :: Int, 
  singletonMap  :: Map.Map Int Int, 
  unionMap      :: Map.Map (Int,Int) Int
}

newHashManager :: HashManager
newHashManager = HashManager 1 Map.empty Map.empty

getHash :: HashManager -> Set -> (HashManager, Int) 
getHash m Empty = (m,0) 


