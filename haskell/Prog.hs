data Term = Var Id | Con Int | Add Term Term
type Id = Int

data Comm = Asgn Id Term | Seq Comm Comm | If Term Comm Comm
data Prog = Prog Comm Term


type State = [Int]
type Ix = Id
type Val = Int

index :: Ix -> State -> Val
index _ []      = error "index: out of bound"
index 0 (x:xs)  = x
index n (x:xs)  = index (n-1) xs

update :: Ix -> Val -> State -> State
update _ _ []     = error "update: out of bound"
update 0 v (x:xs) = v:xs 
update n v (x:xs) = update (n-1) v xs

newArray :: Int -> State
newArray 0  = []
newArray n  = 0 : newArray (n-1) 

newtype M a = M { runM :: State -> (a, State) }

stateM :: (State -> (a, State)) -> M a
stateM = M

instance Monad M where
  return a = stateM $ \s -> (a, s)
  m >>= f  = stateM $ \s -> 
    let (a, t) = runM m s in
      runM (f a) t

load :: Ix -> M Val
load i = stateM $ \s -> (index i s, s)

store :: Ix -> Val -> M ()
store i v = stateM $ \s -> ((), update i v s) 

run :: M a -> a
run m = fst $ runM m (newArray 10) 



-- State reader monad: computation that only read the state

newtype M' a = M' { runM' :: State -> a }

stateM' :: (State -> a) -> M' a
stateM' = M'

instance Monad M' where
  return a  = stateM' $ \_ -> a
  m >>= f   = stateM' $ \s -> 
    let a = runM' m s in
      runM' (f a) s

load' :: Ix -> M' Val
load' i = stateM' $ \s -> index i s

-- A computation which only reads the state is also a computation
-- that may write or read the state. Hence, there should be an embedding

embed :: M' a -> M a
embed m = stateM $ \s -> (runM' m s, s)

-- eval depends on state but does not alter it
eval :: Term -> M' Int      -- read only
eval (Var i)    = load' i
eval (Con a)    = return a
eval (Add t u)  = do
  a <- eval t
  b <- eval u
  return (a + b) 

-- exec may both depend on and alter the state
exec :: Comm -> M ()        -- read / write
exec (Asgn i t)   = embed (eval t) >>= store i
exec (Seq c d)    = exec c >> exec d >> return () 
exec (If t c d)   = do
    a <- embed(eval t)
    if a == 0 
      then exec c 
      else exec d

elab :: Prog -> Int
elab (Prog c t) = run $ do
  exec c
  a <- embed (eval t)
  return a



















