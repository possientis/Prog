module Set (ISet, empty, set, inc, belong, singleton, union, subset, Set()) where
import qualified Data.Map as Map

class ISet a where
  empty     :: a
  singleton :: a -> a
  union     :: a -> a -> a
  belong    :: a -> a -> Bool
  subset    :: a -> a -> Bool
  -- successor
  inc       :: a -> a
  inc x                   = union x (singleton x)
  -- Embedding for natural numbers
  set       :: Int -> a
  set 0                   = empty
  set x                   = inc (set (x - 1))

data Set = Empty | Singleton Set | Union Set Set

instance Show Set where
  show Empty            = "0"
  show (Singleton x)    = "{"++(show x)++"}"
  show (Union x y)      = (show x) ++ "U" ++ (show y)

instance Eq Set where
  (==) x y = (subset x y) && (subset y x)

instance Ord Set where
  (<=) x y = subset x y

instance ISet Set where
  empty                   = Empty
  singleton x             = Singleton x
  union x y               = Union x y

  subset Empty _                      = True  -- (i) 0 <= x forall x
  subset (Singleton x) Empty          = False -- (ii) ¬({x} <= 0) forall x
  subset (Singleton x) (Singleton y)  = (subset x y) && (subset y x)
  subset (Singleton x) (Union y z)    = (subset (Singleton x) y) 
                                      ||(subset (Singleton x) z)
  subset (Union x y) z    = (subset x z) && (subset y z)

  belong x y = subset (Singleton x) y

elements :: Set -> [Set]
elements Empty         = []
elements (Singleton x) = [x]
elements (Union x y)   = elements x ++ elements y

rank :: Set -> Integer
rank Empty          = 0
rank (Singleton x)  = 1 + rank x
rank (Union x y)    = max (rank x) (rank y)

zero      = set 0 :: Set
one       = inc zero 
two       = inc one
three     = inc two
four      = inc three
five      = inc four
six       = inc five
seven     = inc six
eight     = inc seven
nine      = inc eight
ten       = inc nine
eleven    = inc ten
twelve    = inc eleven
 
data HashManager = HashManager {
  nextHash      :: Int, 
  singletonMap  :: Map.Map Int Int, 
  unionMap      :: Map.Map (Int,Int) Int
}

newHashManager :: HashManager
newHashManager = HashManager 1 Map.empty Map.empty


data Hash a = Hash (HashManager -> (a, HashManager))
hashApply :: Hash a -> HashManager -> (a, HashManager)
hashApply (Hash f) manager = f manager

instance Monad Hash where
  return x = Hash (\manager -> (x, manager))
  m >>= k  = Hash (\manager -> 
    let (x, manager') = hashApply m manager in 
      hashApply (k x) manager')

findSingleton :: Int -> Hash (Maybe Int)  
findSingleton h = Hash (\manager -> (Map.lookup h (singletonMap manager), manager))

findUnion :: Int -> Int -> Hash (Maybe Int)
findUnion h h'  = Hash (\manager -> (Map.lookup (h,h')(unionMap manager), manager))

insertSingleton :: Int -> Hash Int
insertSingleton h = Hash (\manager -> let next = nextHash manager in
                    (next, HashManager  (next+1)
                                        (Map.insert h next (singletonMap manager))
                                        (unionMap manager)))

insertUnion :: Int -> Int -> Hash Int
insertUnion h h' = Hash (\manager -> let next = nextHash manager in
                   (next, HashManager (next+1)
                                      (singletonMap manager)
                                      (Map.insert (h,h') next (unionMap manager))))
            
hash :: Set -> Hash Int
hash    Empty           =  return 0
hash   (Singleton x)    =  do hx      <- hash x
                              findx   <- findSingleton hx
                              case findx of
                                Just h    -> return h
                                Nothing   -> insertSingleton hx
hash (Union x y)        =  do hx      <- hash x
                              hy      <- hash y
                              findxy  <- findUnion hx hy
                              case findxy of
                                Just h    -> return h
                                Nothing   -> insertUnion hx hy 


main :: IO()
main = do
  let h0 = hash zero
  let h1 = hash one
  let h2 = hash two
  let manager = newHashManager 

  putStrLn (show (fst (hashApply h0 manager))) 
  putStrLn (show (fst (hashApply h1 manager))) 
  putStrLn (show (fst (hashApply h2 manager))) 





  
