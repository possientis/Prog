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

newtype Predicate a = MkP(a -> Bool)
newPredicate f = MkP f
pNot :: Predicate a -> Predicate a
pNot (MkP f) = MkP (\p -> not (f p))

pAnd :: Predicate a -> Predicate a -> Predicate a
pAnd (MkP f) (MkP g) = MkP (\p -> if not (f p) then False else g p)

pOr :: Predicate a -> Predicate a -> Predicate a
pOr (MkP f) (MkP g) = MkP (\p -> if f p then True else g p)

isEqual :: Person -> Predicate Person
isEqual p = MkP (\q -> (q == p))

data Person = Person {name, gender, maritalStatus :: String}

instance Eq Person where
  (==) p q = let f x = map toUpper (name x) in f p == f q

instance Show Person where
  show p = "("++(name p)++","++(gender p)++","++(maritalStatus p)++")"

male            = newPredicate (\p -> map toUpper (gender p) == "MALE")
female          = newPredicate (\p -> map toUpper (gender p) == "FEMALE")
single          = newPredicate (\p -> map toUpper (maritalStatus p) == "SINGLE")
singleMale      = pAnd single male
singleOrFemale  = pOr single female

people :: [Person]
people =  (Person "Robert" "Male" "Single")  :
          (Person "John" "Male" "Married")   :
          (Person "Laura" "Female" "Married"):
          (Person "Diana" "Female" "Single") :
          (Person "Mike" "Male" "Single")    :
          (Person "Bobby" "Male" "Single")   : []

printList :: [Person] -> IO()
printList []     = return ()
printList (p:ps) = putStr ((show p)++"\t") >> printList ps

filterList :: [Person] -> Predicate Person -> [Person]
filterList ps (MkP f) = filter f ps


john2 = Person "John" "Male" "Married"
notJohn = pNot (isEqual john2)

males           = filterList people male
females         = filterList people female
singleMales     = filterList people singleMale
singleOrFemales = filterList people singleOrFemale
notJohns        = filterList people notJohn
 

main = do
  putStr "Everyone:\t\t"          >> printList people
  putStr "\nNot John:\t\t"        >> printList notJohns
  putStr "\nSingle or Female:\t"  >> printList singleOrFemales
  putStr "\nMales:\t\t\t"         >> printList males
  putStr "\nSingle Males:\t\t"    >> printList singleMales
  putStr "\nFemales:\t\t"         >> printList females
  putStr "\n"



