{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE UndecidableInstances   #-}

import Data.Kind
import GHC.TypeLits     (Nat)

-- Given a kind k, defines a kind 'Exp k'
type Exp k = k -> Type

-- A type 'e' of kind 'Exp k' can be evaluated as a type of kind k
-- Signature for type-level function Eval :: Exp k -> k
-- But no implementation provided for this type-level function
-- Defined as an open type family
type family Eval (e :: Exp k) :: k

data A (a :: k) :: k

-- Given two kinds k1 k2, given a type of kind (k1,k2), 
-- creates a type of kind Exp k2
data Snd :: forall k1 k2. (k1,k2) -> Exp k2

-- Same with GADTs syntax?
data Snd' (a :: (k1,k2)) :: Exp k2

-- So both Ex1 and Ex1' are types of kind 'Exp *'
type Ex1  = Snd  '(Int,String)
type Ex1' = Snd' '(Int,String) 

type instance Eval (Snd  '(a,b)) = b
type instance Eval (Snd' '(a,b)) = b

-- Ex2 and Ex2' are the type '[Char]' of kind '*'
type Ex2  = Eval Ex1
type Ex2' = Eval Ex1'

-- Given a kind 'k', and two types 'a' 'b' of kind 'k' and 
-- Maybe k respectively, creates a type of kind 'Exp k'.
data FromMaybe :: forall k. k -> Maybe k -> Exp k
data FromMaybe' (a :: k) (b :: Maybe k) :: Exp k

-- So both Ex3 and Ex3' are types of kind 'Exp *'
type Ex3  = FromMaybe  Int ('Just Double)
type Ex3' = FromMaybe' Int ('Just Double)  

-- and both Ex4 and Ex4' are types of kind 'Exp *'
type Ex4  = FromMaybe Int ('Nothing )
type Ex4' = FromMaybe Int ('Nothing )

type instance Eval (FromMaybe  _ ('Just a))  = a
type instance Eval (FromMaybe' _ ('Just a))  = a

type instance Eval (FromMaybe  a 'Nothing)   = a
type instance Eval (FromMaybe' a 'Nothing)   = a

-- Ex5 and Ex5' are the type 'Double' of kind '*'.
type Ex5  = Eval Ex3
type Ex5' = Eval Ex3'

-- Ex6 and Ex6' are the type 'Int' of kind '*'.
type Ex6  = Eval Ex4
type Ex6' = Eval Ex4'

-- Given a kind 'k', and a type 'a' of kind '[k]',
-- creates a type of kind 'Exp (Maybe k)'
data ListToMaybe :: forall k. [k] -> Exp (Maybe k)
data ListToMaybe' (as :: [k]) :: Exp (Maybe k)


-- So both Ex7 and Ex7' are types of kind 'Exp (Maybe *)'
type Ex7  = ListToMaybe  '[Char, String, Int, Double]
type Ex7' = ListToMaybe' '[Char, String, Int, Double]

-- Ex8 and Ex8' are also types of kind 'Exp (Maybe *)'
type Ex8   = ListToMaybe  ('[] :: [*])
type Ex8'  = ListToMaybe' ('[] :: [*])

type instance Eval (ListToMaybe  '[])   = 'Nothing
type instance Eval (ListToMaybe' '[])   = 'Nothing

type instance Eval (ListToMaybe  (a ': as))  = 'Just a
type instance Eval (ListToMaybe' (a ': as))  = 'Just a

-- Ex9 and Ex9' are the type ' 'Just [Char] ' of kind 'Maybe *'
type Ex9  = Eval Ex7
type Ex9' = Eval Ex7'

-- Ex10 and Ex10' are the type ' 'Nothing ' of kind 'Maybe *'
type Ex10  = Eval Ex8
type Ex10' = Eval Ex8'

-- Given two kinds 'k1' and 'k2', a type 'f' of kind 'k1 -> Exp k2'
-- a type 'as' of kind '[k1]', creates a type of kind 'Exp [k2]'
data MapList :: forall k1 k2. (k1 -> Exp k2) -> [k1] -> Exp [k2]
data MapList' (f :: k1 -> Exp k2) (as :: [k1]) :: Exp [k2]

-- So both Ex11 and Ex11' are types of kind 'Exp [*]'
type Ex11  = MapList Snd '[ '(Int,Char), '(Double, String) ] 
type Ex11' = MapList Snd '[ '(Int,Char), '(Double, String) ] 

type instance Eval (MapList  f '[]) = '[]
type instance Eval (MapList' f '[]) = '[]

type instance Eval (MapList  f (a ': as)) = Eval (f a) ': Eval (MapList  f as)
type instance Eval (MapList' f (a ': as)) = Eval (f a) ': Eval (MapList' f as)

-- Ex12 and Ex12' are the type ' '[Char, [Char]] ' of kind '[*]'
type Ex12  = Eval Ex11
type Ex12' = Eval Ex11'

-- Ex13 and Ex13' are the type ' '[0,1] ' of kind '[Nat]'
type Ex13  = Eval (MapList  (FromMaybe  0) '[ 'Nothing, 'Just 1 ] )
type Ex13' = Eval (MapList' (FromMaybe' 0) '[ 'Nothing, 'Just 1 ] )

-- Given two kinds 'k1' and 'k2', a type 'op' of kind 'k1 -> k2 -> Exp k2'
-- a type 'b' of kind k2 and a type 'as' of kind '[k1]',
-- creates a type of kind 'Exp k2'
data Foldr  :: forall k1 k2. (k1 -> k2 -> Exp k2) -> k2 -> [k1] -> Exp k2
data Foldr' (op :: k1 -> k2 -> Exp k2) (b :: k2) (as :: [k1]) :: Exp k2

data Append (xs :: [Nat]) (ys :: [Nat]) :: Exp [Nat]

type instance Eval (Append '[] ys)       = ys
type instance Eval (Append (x ': xs) ys) = x ': (Eval (Append xs ys))

type instance Eval (Foldr  op init '[])       = init 
type instance Eval (Foldr' op init '[])       = init 

type instance Eval (Foldr  op init (a ': as)) = Eval (op a (Eval (Foldr  op init as)))
type instance Eval (Foldr' op init (a ': as)) = Eval (op a (Eval (Foldr' op init as)))


-- Ex14 and Ex14' are types of kind 'Exp [Nat]'
type Ex14  = Foldr  Append '[] '[ '[0, 1, 2], '[3, 4], '[5] ]
type Ex14' = Foldr' Append '[] '[ '[0, 1, 2], '[3, 4], '[5] ]

-- Ex15 and Ex15' are the type ' '[0,1,2,3,4,5] ' of kind '[Nat]'
type Ex15  = Eval Ex14
type Ex15' = Eval Ex14' 


data Pure :: k -> Exp k
data Pure' (a :: k) :: Exp k

type instance Eval (Pure a) = a

data (=<<) :: (k1 -> Exp k2) -> Exp k1 -> Exp k2
type instance Eval (f =<< e) = Eval (f (Eval e))

data (>>=) (a :: Exp k1) (f :: k1 -> Exp k2) :: Exp k2
type instance Eval (e >>= f) = Eval (f (Eval e))

infixl 0 >>=
infixr 0 =<<

data (>=>) 
  :: (a -> Exp b)
  -> (b -> Exp c)
  -> (a -> Exp c)

type instance Eval ((f >=> g) x) = Eval (f x >>= g)

data TyEq :: a -> b -> Exp Bool

type instance Eval (TyEq a b) = TyEqImpl a b

type family TyEqImpl (a :: k) (b :: k) :: Bool where
    TyEqImpl a a = 'True
    TyEqImpl a b = 'False

data Collapse :: [Constraint] -> Exp Constraint

type instance Eval (Collapse '[]) = (() :: Constraint)
type instance Eval (Collapse (a ': as)) = (a, Eval (Collapse as))

data Pure1 :: (a -> b) -> a -> Exp b
type instance Eval (Pure1 f x) = f x

type All (c :: k -> Constraint) (ts :: [k]) = MapList (Pure1 c) ts >>= Collapse

type Ex16 = Eval (All Eq '[Int, Bool])


data Map :: (a -> Exp b) -> f a -> Exp (f b)

type instance Eval (Map f '[]) = '[]
type instance Eval (Map f (a ': as)) = Eval (f a) ': Eval (Map f as)

type instance Eval (Map f 'Nothing)  = 'Nothing
type instance Eval (Map f ('Just a)) = 'Just (Eval (f a)) 

type instance Eval (Map f ('Left x))  = 'Left x
type instance Eval (Map f ('Right x)) = 'Right (Eval (f x)) 

type Ex17 = Eval (Map Snd ('Just '(1,2))) -- 'Just 2 :: Maybe Nat

type Ex18 = Eval (Map Snd '[ '(1,2) ])    -- '[2] :: [Nat]

type Ex19 = Eval (Map Snd ('Left 'False)) -- 'Left 'False :: Either Bool k


data Mappend :: a -> a -> Exp a

type instance Eval (Mappend '() '()) = '()

type instance Eval (Mappend (a :: Constraint) (b :: Constraint)) = (a,b)


data (++) (as :: [k]) (bs :: [k]) :: Exp [k]

type instance Eval ('[] ++ bs) = bs
type instance Eval ((a ': as) ++ bs) = a ': (Eval (as ++ bs))

type instance Eval (Mappend (as :: [k]) (bs :: [k])) = Eval (as ++ bs)




