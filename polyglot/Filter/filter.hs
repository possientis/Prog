-- Filter design pattern
import Data.Char  -- toUpper
-- This pattern allows to use a list of objects and perform
-- a filtering operation on that list so as to obtain a new
-- list comprised of those objects in the initial list which
-- satisfy a given predicate. Since the introduction of
-- lambda expressions within Java 8 and the introduction
-- of functional interfaces such as Predicate<T>, this 
-- pattern is not very useful in practice and amounts 
-- mainly to a coding exercise aiming at re-implementing
-- the Predicate<T> java interface. This pattern is not
-- useful either in functional languages which directly 
-- support first class functions and filter operations on lists.

class (Eq a) => IPredicate p a where
  -- public interface
  test    :: p a -> a -> Bool
  make    :: (a -> Bool) -> p a
  pNot    :: p a -> p a
  pAnd    :: p a -> p a -> p a
  pOr     :: p a -> p a -> p a
  isEqual :: a -> p a
  -- default implementation
  pNot p    = make (\x -> not (test p x))
  pAnd p q  = make (\x -> (test p x) && (test q x))
  pOr  p q  = make (\x -> (test p x) || (test q x))
  isEqual a = make (\x -> x == a)

class (Eq a, Show a)  =>  IPerson a where
  -- public interface
  name            :: a -> String
  gender          :: a -> String
  maritalStatus   :: a -> String
  people          :: [a]
  printList       :: [a] -> IO()
  filterList      :: [a] -> Predicate a -> [a]
  male            :: Predicate a
  female          :: Predicate a
  single          :: Predicate a
  singleMale      :: Predicate a
  singleOrFemale  :: Predicate a
  -- default implementation
  male   = make (\x -> map toUpper (gender x) == "MALE") 
  female = make (\x -> map toUpper (gender x) == "FEMALE") 
  single = make (\x -> map toUpper (maritalStatus x) == "SINGLE") 
  singleMale      = pAnd single male
  singleOrFemale  = pOr single female
  printList []  = return()
  printList (p:ps) = putStr ((show p)++"\t") >> printList ps
  filterList ps pred = filter (\x -> test pred x) ps


newtype Predicate a = Predicate (a -> Bool) 
instance (Eq a) => IPredicate Predicate a where 
  test (Predicate p) = p
  make f = Predicate f

data Person = Person String String String
instance IPerson Person where
  name          (Person x _ _) = x
  gender        (Person _ x _) = x
  maritalStatus (Person _ _ x) = x
  people =      (Person "Robert" "Male" "Single")  :
                (Person "John" "Male" "Married")   :
                (Person "Laura" "Female" "Married"):
                (Person "Diana" "Female" "Single") :
                (Person "Mike" "Male" "Single")    :
                (Person "Bobby" "Male" "Single")   : []

instance Eq Person where
  p1 == p2  = map toUpper (name p1) == map toUpper (name p2)

instance Show Person where
  show (Person name gender ms) = "(" ++ name ++ "," ++ gender ++ "," ++ ms ++ ")"

john2 = Person "John" "Male" "Married"
notJohn = pNot (isEqual john2)

people'         = people::[Person]
males           = filterList (people') male
females         = filterList (people') female
singleMales     = filterList (people') singleMale
singleOrFemales = filterList (people') singleOrFemale
notJohns        = filterList (people') notJohn

main = do
  putStr "Everyone:\t\t"          >> printList people'
  putStr "\nNot John:\t\t"        >> printList notJohns
  putStr "\nSingle or Female:\t"  >> printList singleOrFemales
  putStr "\nMales:\t\t\t"         >> printList males
  putStr "\nSingle Males:\t\t"    >> printList singleMales
  putStr "\nFemales:\t\t"         >> printList females
  putStr "\n"






