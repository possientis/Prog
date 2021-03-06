-- Flyweight Design Pattern
import qualified Data.Map as Map
import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))

-- The main idea of the flyweight design pattern is to store objects
-- in a dictionary so they can be reused, rather than new objects be
-- created. This pattern is particularly well suited to classes of 
-- immutable objects which is the case we shall consider here. Because
-- dictionaries cannot exist without keys, the flyweight design pattern
-- is closely related to the question of hashing.
--
-- We shall consider the example of an inductive type Set with the three
-- constructors (i) Zero : Set,  (ii) Singleton : Set-> Set and (iii)
-- Union : Set -> Set -> Set. The type Set therefore corresponds to 
-- the free algebra generated by a single element 0 (the empty set) and
-- the operators x -> {x} and x,y -> xUy. Although, the questions of preorder
-- (inclusion) and equivalence between sets are very important, we shall 
-- not consider it here and simply look at elements of type Set as syntactic
-- objects. A typical OOP implementation is based on the composite  design 
-- pattern which we shall adopt in this example.
--
-- Objects (which are immutable) are supposed to be reused, not created.
-- So the constructors of the type Set should not be used directly. Instead, 
-- the class should provide static factory functions for 0, {x] and xUy. 
--
-- Fundamentally, we need to maintain a dictionary of created objects and
-- we shall design a separate class SetManager to handle this dictionary.
-- 
-- It is possible to consider static algorithms for hash values. However, 
-- these often do not guarantee that two objects are equal. It is nice to
-- know that a static hash function is a (mathematically) injective mapping.
-- In the case at hand, such function exist but are computationally unusable
-- due to their rapid growth. Using dynamic hashing, although not specifically
-- called for by the flyweight design pattern, provides the convenience of 
-- producing truly unique hashes, which grow very slowly (a hash counter
-- is incremented at each object creation). 
--
-- So this example illustrate a case of flyweight design pattern, as well
-- as proposing a scheme for the generation of dynamic hash values. 
--
-- This Haskell implementation differs from other languages. We already have 
-- the notion of abstract data type and there is no need to attempt replicating
-- the standard composite design pattern of traditional OOP languages. Furthermore
-- we have made an attempt at modelling the side effects inherent to the problem
-- (each object retrieval potentially changes the state of the set manager)   
-- with a 'monadic style'. So we created a monadic type from SetManager.

data Set = Zero | Singleton Set Int | Union Set Set Int

hashCode :: Set -> Int
hashCode    Zero                = 0
hashCode   (Singleton  _ hash)  = hash 
hashCode   (Union    _ _ hash)  = hash

instance  Show Set where
  show    Zero            = "0"
  show   (Singleton x _)  = "{" ++ (show x) ++ "}"
  show   (Union   x y _)  = (show x) ++ "U" ++ (show y) 


-- In traditional OOP languages, each type constructor would have two associated
-- factory methods: one as part of the Set interface, which delegates its call
-- to a second as part of the set manager interface. There is no need for this
-- duplication in Haskell. The factory method requires standard arguments of
-- type Set, as well as a set manager object. The latter dependency is hidden
-- through the monadic style.
--
-- The manager maintains various dictionaries. The main dictionary is objectMap,
-- which given a hash code, returns a previously constructed object. However,
-- The manager needs to implement the factory methods corresponding to the 
-- three constructors of the inductive type Set. Implementing the zero()
-- method is easy. The manager always assigns 0 as its hash code and creates
-- a single object which is stored once and for all in the objectMap dictionary.
-- The method zero() simply returns a reference to the existing object.
-- In order to implement singleton(x) (returning the object {x} from x), the 
-- manager needs to quickly establish whether (given the set x and its hash code)
-- the set {x} has already been created. However, the manager cannot simply query
-- the objectMap dictionary because it does not know what dynamic hash code the
-- singleton {x} was assigned (assuming it already exists). This is why the manager
-- maintains an additional dictionary 'singletonMap' which stores the hash code
-- of {x} given the hash code of x. Hence by querying the dictionary singletonMap,
-- the manager is able to establish whether {x} already exists, and if so, what its
-- hash code is. Given the hash code of {x} it can simply query objectMap and
-- return the appropriate object. In the case when the object {x} does not already 
-- exist, the manager assigns the current value of 'nextHash' to the object {x}, 
-- then creates the object using this hash value, and before it returns the object,
-- the manager updates objectMap with the new object and singletonMap with the 
-- link between the hash of x and that of {x}. In order to implement the factory 
-- method union(x,y), a similar scheme is adopted which requires a new dictionary
-- unionMap. This map could have been implemented with pairs as keys, but we 
-- decided to keep using integers, and simply map pairs of ints to ints with 
-- the Cantor function.
 
data SetManager = SetManager {
  nextHash      :: Int,
  singletonMap  :: Map.Map Int Int,
  unionMap      :: Map.Map Int Int,
  objectMap     :: Map.Map Int Set
}

-- new manager has Zero saved in object dictionary with hash code of 0
newManager = SetManager 1 Map.empty Map.empty (Map.insert 0 Zero Map.empty)

-- the type constructors have side effects (as they modify the state of 
-- the set manager. Hence, contrary to the implementation in other languages
-- the type constructors return a monadic value rather than a value of type Set.
-- We could have made zero of type Set, but decided to be consistent accross all
-- constructors. The monadic type 'SM Set' can be thought of as a computation
-- (not yet executed) which returns a Set. As will be seen below, it is simply
-- a map of type SetManager -> (Set, SetManager) which takes a 'state of the 
-- world' as input (i.e. some set manager) and returns a Set, together with a 
-- new 'state of the world' (a new set manager representing the updated set 
-- manager following the computation).

-- zero
zero :: SM Set
zero = do 
  maybe <- getObject 0
  case maybe of 
    Just z  -> return z
    Nothing -> error "The set manager has not been properly initialized"

-- singleton
singleton :: Set -> SM Set
singleton x = do
  let hash = hashCode x
  mappedHash <- getSingletonHash hash   -- finding out whether {x} exists
  case mappedHash of
    Nothing   -> do                     -- singleton {x} is unknown
      newHash <- getNextHash            -- next available hash value
      putSingletonHash hash newHash     -- new hash value is allocated to {x}
      let object = Singleton x newHash  -- creating {x}
      putObject newHash object          -- saving {x} for future reference
      incNextHash                       -- incrementing next available hash value
      return object
    Just mappedHash'  -> do             -- singleton {x} is known
      object <- getObject mappedHash'   -- simply retrieve object from its hash
      case object of
        Nothing   -> error "Set manager has inconsistent state"
        Just set  -> return set         

pairingCantor :: Int -> Int -> Int
pairingCantor x y = y + div ((x + y + 1)*(x + y)) 2
--
-- union
union :: Set -> Set -> SM Set 
union x y = do
  let hx = hashCode x
  let hy = hashCode y
  let hash = pairingCantor hx hy
  mappedHash <- getUnionHash hash       -- finding out whether xUy exists 
  case mappedHash of
    Nothing -> do                       -- union xUy is unknown
      newHash <- getNextHash            -- next available hash value 
      putUnionHash hash newHash         -- new hash value is allocated to xUy
      let object = Union x y newHash    -- creating xUy
      putObject newHash object          -- saving xUy for future reference 
      incNextHash                       -- incrementing next available hash value
      return object
    Just mappedHash'  -> do             -- union xUy is known
      object <- getObject mappedHash'   -- simply retrieve object from its hash
      case object of
        Nothing   -> error "Set manager has inconsistent state"
        Just set  -> return set

-- successor, example of the use of the binding operator (>>=) of the monad SM 
successor :: Set -> SM Set
successor x = singleton x >>= (\y -> union x y)


-- The rest of the code is implementation of the monadic type together with that
-- of the various functions which are used above.

data SM a = SM (SetManager -> (a, SetManager))

apply :: SM a -> SetManager -> (a, SetManager)
apply (SM f) manager = f manager

instance Monad SM where 
  return x = SM (\manager -> (x, manager))
  m >>= k  = SM (\manager -> let (x, tempManager) = apply m manager 
                             in apply (k x) tempManager)
-- needed to compile
instance Functor SM where
  fmap = liftM
-- needed to compile
instance Applicative SM where
  pure = return
  (<*>) = ap



-- returns object corresponding to hash value
getObject :: Int -> SM (Maybe Set)
getObject hash = SM (\manager -> (Map.lookup hash (objectMap manager), manager))

-- saves object under the given hash value
putObject :: Int -> Set -> SM ()
putObject hash mappedSet = SM (\manager -> ((), SetManager
  (nextHash manager)(singletonMap manager)(unionMap manager)
  (Map.insert hash mappedSet (objectMap manager))))


-- returns hash value of singleton {x} from hash value of x, assuming {x} exists 
getSingletonHash :: Int -> SM (Maybe Int)
getSingletonHash hash = SM (\manager -> (Map.lookup hash (singletonMap manager), 
                                          manager))

-- saves the link between the hash of x and that of {x}
putSingletonHash :: Int -> Int -> SM ()
putSingletonHash hash mappedHash = SM (\manager -> ((), SetManager 
  (nextHash manager) (Map.insert hash mappedHash (singletonMap manager))
  (unionMap manager) (objectMap manager)))  

-- returns hash value of union xUy from hash of the pair (x,y)
getUnionHash :: Int -> SM (Maybe Int)
getUnionHash hash = SM (\manager -> (Map.lookup hash (unionMap manager), manager))
  
-- saves the link between the hash of the pair (x,y) and that of xUy
putUnionHash :: Int -> Int -> SM ()
putUnionHash  hash mappedHash = SM (\manager -> ((), SetManager
  (nextHash manager) (singletonMap manager)
  (Map.insert hash mappedHash (unionMap manager))
  (objectMap manager)))

-- value of of hash to be allocated next
getNextHash :: SM Int
getNextHash = SM (\manager -> (nextHash manager, manager))

-- increments next hash value
incNextHash :: SM ()
incNextHash = SM (\manager ->  ((), SetManager
  ((nextHash manager) + 1) (singletonMap manager)
  (unionMap manager) (objectMap manager)))
                          

-- returns output string
debug :: SM String
debug = SM (\manager -> 
  (foldr (++) ""  
    (map  
      (\i -> 
        "hash = " ++ (show i) ++ ": " ++
          (let object = Map.lookup i (objectMap manager) in 
            case object of
              Nothing   ->  error "Set manager is failing"
              Just set  -> (show set)) ++ 
              (if i == ((nextHash manager) -1) then "" else "\n")) 
      [0..((nextHash manager) - 1)]
    ), manager))

flyweight :: SM String
flyweight = do
  zero' <- zero
  one   <- successor zero'  
  two   <- successor one
  three <- successor two
  four  <- successor three
  five  <- successor four
  debug

run :: SM String -> IO()
run m = do
  let (str, manager) = apply m newManager in
    putStrLn str

main = run flyweight


