import qualified Data.Map as Map
data Set = Zero | Singleton Set Int | Union Set Set Int


data SetManager = SetManager {
  nextHash      :: Int,
  singletonMap  :: Map.Map Int Int,
  unionMap      :: Map.Map (Int, Int) Int,
  objectMap     :: Map.Map Int Set
}
