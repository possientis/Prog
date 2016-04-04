import qualified Data.Map as Map

data Set = Zero | Singleton Set Int | Union Set Set Int

hashCode :: Set -> Int
hashCode  Zero                = 0
hashCode (Singleton  _ hash)  = hash 
hashCode (Union    _ _ hash)  = hash

-- the type constructors have side effects (as they modify the state of 
-- the set manager. Hence, contrary to the implementation in other languages
-- the type constructors return a monadic value rather than a value of type Set.
-- We could have made zero of type Set, but decided to be consistent. 

zero :: SM Set
zero = do
  maybe <- getObject 0
  case maybe of 
    Just z  -> return z
    Nothing -> error "The set manager has not been properly initialized"
{-
singleton :: Set -> SM Set
singleton x = do
  let hash = hashCode x
  mappedHash <- getSingletonHash hash
  case mappedHash of
    Nothing   -> do
      putSingleton
-}





data SetManager = SetManager {
  nextHash      :: Int,
  singletonMap  :: Map.Map Int Int,
  unionMap      :: Map.Map Int Int,
  objectMap     :: Map.Map Int Set
}

-- new manager has Zero saved in object dictionary with hash code of 0
newManager = SetManager 1 Map.empty Map.empty (Map.insert 0 Zero Map.empty)

-- creating a monadic type to simulate side effects: state is a manager object
data SM a = SM (SetManager -> (a, SetManager))

-- monad implementation requires an apply function
apply :: SM a -> SetManager -> (a, SetManager)
apply (SM f) manager = f manager

-- actual monad implementation
instance Monad SM where 
  return x = SM (\manager -> (x, manager))
  m >>= k  = SM (\manager -> let (x, tempManager) = apply m manager 
                             in apply (k x) tempManager)

-- returns object from hash value. Return type is monadic, as accesses the 'state'
getObject :: Int -> SM (Maybe Set)
getObject hash = SM (\manager -> (Map.lookup hash (objectMap manager), manager))


-- returns hash value of singleton {x} from hash value of x, assuming {x} exists 
-- return type is monadic as it accesses the 'state' represented by the set manager
getSingletonHash :: Int -> SM (Maybe Int)
getSingletonHash hash = SM (\manager -> 
                           (Map.lookup hash (singletonMap manager), manager))

-- return newly created object {x}, given the hash code of x
newSingleton :: Int -> SM Set


-- returns hash value of union xUy from hash values of x and y, assuming xUy exists
-- return type is monadic as it accesses the 'state' represented by the set manager
getUnionHash :: Int -> Int -> SM (Maybe Int)
getUnionHash hx hy = SM (\manager -> let hash = pairingCantor hx hy in
                        (Map.lookup hash (unionMap manager), manager))
  
pairingCantor :: Int -> Int -> Int
pairingCantor x y = y + div ((x + y + 1)*(x + y)) 2

