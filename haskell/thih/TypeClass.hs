module  TypeClass
    (   q1
    ,   main
    ,   ord
    ,   mguPred
    ,   matchPred
    ,   Inst
    ,   Class
    ,   ClassEnv (..)
    ,   super
    ,   insts
    ,   defined
    ,   modify
    ,   initialEnv
    ,   (<:>)
    ,   addClass
    ,   addPreludeClasses
    ,   addInst
    ,   bySuper
    ,   byInst
    ,   entail
    )   where

import Subst
import Syntax

import Data.List
import Data.Maybe
import Control.Monad (msum)

data Pred = IsIn Id Type deriving Eq

data Qual t = [Pred] :=> t deriving Eq

-- a -> Int
t1 :: Type
t1 =  TVar (Tyvar "a" Star) `fn` tInt

-- (Num a) => a -> Int
q1 :: Qual Type
q1 = [IsIn "Num" (TVar (Tyvar "a" Star))] :=> t1

instance Types Pred where
    apply s (IsIn i t)   = IsIn i (apply s t)
    tv (IsIn _ t)        = tv t

instance (Types t) => Types (Qual t) where
    apply s (ps :=> t)  = apply s ps :=> apply s t
    tv (ps :=> t)       = tv ps `union` tv t

lift :: (Monad m) => (Type -> Type -> m Subst) -> Pred -> Pred -> m Subst
lift m (IsIn i t) (IsIn i' t')
    | i == i'       = m t t'
    | otherwise     = fail "lift: classes differ" 

mguPred :: (Monad m) => Pred -> Pred -> m Subst
mguPred = lift mgu

matchPred :: (Monad m) => Pred -> Pred -> m Subst
matchPred = lift match

-- So an instance is a list of predicates, and a predicate ?
type Inst = Qual Pred

-- A Class is a pair of lists: 
-- 1. list of superclass 2. entry for each instance declaration
type Class = ([Id],[Inst])

-- class Eq a => Ord a where ... (Eq is a superclass of Ord)
-- instance Ord () where ...
-- instance Ord Char where ...
-- instance Ord Int where
-- instance (Ord a, Ord b) => Ord (a, b) where ...
ord :: Class
ord = ( ["Eq"]
      , [ [] :=> IsIn "Ord" tUnit
        , [] :=> IsIn "Ord" tChar
        , [] :=> IsIn "Ord" tInt
        , [ IsIn "Ord" (TVar (Tyvar "a" Star))
          , IsIn "Ord" (TVar (Tyvar "b" Star))
          ]  :=> IsIn "Ord" 
                ( pair  (TVar (Tyvar "a" Star)) 
                        (TVar (Tyvar "b" Star))
                ) 
        ]
      )


data ClassEnv = ClassEnv 
    { classes  :: Id -> Maybe Class
    , defaults :: [Type]
    }

super :: ClassEnv -> Id -> [Id]
super ce i = case classes ce i of 
    Just (is,_) -> is
    Nothing -> error "super: argument is not a class identifier"

insts :: ClassEnv -> Id -> [Inst]
insts ce i = case classes ce i of 
    Just (_,its) -> its
    Nothing -> error "insts: argument is not a class identifier"

defined :: Maybe a -> Bool
defined = isJust

modify :: ClassEnv -> Id -> Class -> ClassEnv
modify ce i c = ce { classes = \j -> if i == j then Just c else classes ce j }

initialEnv :: ClassEnv
initialEnv =  ClassEnv 
    { classes = const Nothing
    , defaults = [tInteger, tDouble] 
    }

type EnvTransformer = ClassEnv -> Maybe ClassEnv

infixr 5 <:>
(<:>) :: EnvTransformer -> EnvTransformer -> EnvTransformer
(f <:> g) ce = do { ce' <- f ce ; g ce' }

addClass :: Id -> [Id] -> EnvTransformer
addClass i is ce
    | defined (classes ce i)              = Nothing -- class is already defined 
    | any (not . defined . classes ce) is = Nothing -- one superclass not defined
    | otherwise                           = Just $ modify ce i (is,[])

addPreludeClasses :: EnvTransformer
addPreludeClasses = addCoreClasses <:> addNumClasses


addCoreClasses :: EnvTransformer
addCoreClasses  =  addClass "Eq"            []
               <:> addClass "Ord"           ["Eq"]
               <:> addClass "Show"          []
               <:> addClass "Read"          []
               <:> addClass "Bounded"       []  
               <:> addClass "Enum"          []
               <:> addClass "Functor"       []
               <:> addClass "Applicative"   ["Functor"]
               <:> addClass "Monad"         ["Applicative"]
             
addNumClasses :: EnvTransformer
addNumClasses   =  addClass "Num"           ["Eq","Show"]
               <:> addClass "Real"          ["Num","Ord"]
               <:> addClass "Fractional"    ["Num"]
               <:> addClass "Integral"      ["Real","Enum"]
               <:> addClass "RealFrac"      ["Real", "Fractional"]
               <:> addClass "Floating"      ["Fractional"]
               <:> addClass "RealFloat"     ["RealFrac","Floating"] 

addInst :: [Pred] -> Pred -> EnvTransformer
addInst ps p@(IsIn i _) ce
    | not (defined (classes ce i))  = Nothing -- no class for instance
    | any (overlap p) qs            = Nothing -- overlapping instance
    | otherwise                     = Just $ modify ce i c
    where
    its = insts ce i
    qs  = [q | (_ :=> q) <- its]
    c   = (super ce i, (ps :=> p) : its)

overlap :: Pred -> Pred -> Bool
overlap p q = defined (mguPred p q)


exampleInsts :: EnvTransformer
exampleInsts    =  addPreludeClasses
               <:> addInst [] (IsIn "Ord" tUnit) 
               <:> addInst [] (IsIn "Ord" tChar)
               <:> addInst [] (IsIn "Ord" tInt)
--             This would create an overlapping instance
--             <:> addInst [] (IsIn "Ord" (pair tInt tInt))
               <:> addInst [IsIn "Ord" (TVar (Tyvar "a" Star))
                           ,IsIn "Ord" (TVar (Tyvar "b" Star))
                           ]  (IsIn "Ord" 
                                (pair (TVar (Tyvar "a" Star)) 
                                      (TVar (Tyvar "b" Star))))
                                          
exampleCE :: Maybe ClassEnv
exampleCE = exampleInsts initialEnv


-- If a type t is an instance of class i, it must be an instance of
-- any super class of i , and any super class of any super class of i ...
-- So from a class environment and a predicate, we deduce many other 
-- predicates. The super class hierarchy is restricted to being acyclic
-- so bySuper ce p will always be finite.

bySuper :: ClassEnv -> Pred -> [Pred]
bySuper ce p@(IsIn i t) = p : concat [bySuper ce (IsIn i' t) | i' <- super ce i]


-- Given a class environment ce and knowledge of a predicate telling us that
-- 'type t is an instance of class i', we may deduce other predicates: 
-- 'insts ce i' gives us the list of all instances declarations of the class
-- i in the environment ce. We go through this list of declarations. For
-- each declaration p :=> h we look if the declaration head 'h' matches
-- our predicate (so the predicate holds because of such declaration 
-- and only because of such declaration as haskell prevents overlapping
-- instances. When we find a matching head, we obtain the corresponding
-- substitution which we apply to all the constraints, which are the 
-- predicates which can be inferred
byInst :: ClassEnv -> Pred -> Maybe [Pred]
byInst ce p@(IsIn i _) = msum [tryInst it | it <- insts ce i]
    where tryInst (ps :=> h) = do 
            u <- matchPred h p
            Just (map (apply u) ps)

-- entail ce ps p will be True, if and only if the predicate p will
-- hold whenever all the predicates ps are satisfied:

entail :: ClassEnv -> [Pred] -> Pred -> Bool
entail ce ps p = any (p `elem`) (map (bySuper ce) ps) || 
    case byInst ce p of
        Nothing -> False
        Just qs -> all (entail ce ps) qs


main :: IO ()
main = case exampleCE of
    Nothing -> putStrLn "failed"
    Just _  -> putStrLn "succeeded"
