
data Term = Con Int | Div Term Term deriving (Show)


{- simple evaluator -}

newtype M0 a = M0 { runM0 :: a } deriving (Show)

state0 :: a -> M0 a
state0 = M0

eval0 :: Term -> M0 Int
eval0 (Con a)    = M0 a
eval0 (Div t u)  = M0 $ div (runM0$ eval0 t) (runM0 $ eval0 u)

test0  = (Div (Con 1) (Con 0))
test1  = (Div (Div (Con 1972) (Con 2)) (Con 23))

instance Monad M0 where
  return = state0 
  m >>= f = state0 $ (runM0 . f . runM0) m

eval0' :: Term -> M0 Int
eval0' = eval


{- evaluator with exception handling -}

data M1 a = Raise Exception | Return a deriving (Show)
type Exception = String

eval1 :: Term -> M1 Int
eval1 (Con a) = Return a
eval1 (Div t u) = 
  case eval1 t of
    Raise e     -> Raise e
    Return a    -> 
      case eval1 u of
        Raise e   -> Raise e
        Return b  -> 
          if b == 0 
            then Raise "divide by zero"
            else Return (div a b)  

instance Monad M1 where
  return a = Return a
  m >>= f = 
    case m of 
      Raise e -> Raise e
      Return a -> f a

eval1' :: Term -> M1 Int
eval1' = eval


{- evaluator with state counter -}

newtype M2 a = M2 { runM2 :: State -> (a, State) }
type State = Int

state2 :: (State -> (a, State)) -> M2 a
state2 = M2

eval2 :: Term -> M2 Int
eval2 (Con a)   = state2 $ \x -> (a, x)
eval2 (Div t u) = state2 $ \x ->
  let (a, y) = runM2 (eval2 t) x in
    let (b, z) = runM2 (eval2 u) y in
      (div a b, z + 1)

instance Monad M2 where
  return a = state2 $ \x -> (a, x)
  m >>= f = state2 $ \x -> 
    let (a, y) = runM2 m x in
      runM2 (f a) y

{- we cannot reuse the generic 'eval' here as we need to
 - introduce an additional action incCounter in the code -}
eval2' :: Term -> M2 Int
eval2' (Con a) = return a
eval2' (Div t u) = do
  a <- eval2' t
  b <- eval2' u
  incCounter
  return $ div a b

incCounter :: M2 ()
incCounter = state2 $ \x -> ((), x + 1)




{- evaluator with trace report -}

newtype M3 a = M3 { runM3 :: (Output, a) }
type Output = String

state3 :: (Output, a) -> M3 a
state3 = M3

trace :: M3 a -> IO ()
trace = putStrLn . fst . runM3

result :: M3 a -> a
result = snd . runM3

eval3 :: Term -> M3 Int
eval3 (Con a) = state3 (line (Con a) a, a)
eval3 (Div t u) = state3 $  
  let (x, a) = runM3 $ eval3 t in
    let (y, b) = runM3 $ eval3 u in
      (x ++ y ++ line (Div t u) (div a b), div a b)

line :: (Show a, Integral a) => Term -> a -> Output
line t a = "eval(" ++ (show t) ++ ") <= " ++ (show a) ++ "\n"

instance Monad M3 where
  return a  = state3 $ ("", a)
  m >>= f   = state3 $ 
    let (x, a) = runM3 m in
      let (y, b) = runM3 (f a) in
        (x ++ y, b) 

out :: Output -> M3 ()
out msg = state3 $ (msg, ())

eval3' :: Term -> M3 Int
eval3' (Con a) = do
  out $ line (Con a) a
  return a
eval3' (Div t u) = do
  a <- eval3' t
  b <- eval3' u
  out $ line (Div t u) (div a b)
  return $ div a b



eval :: Monad m => Term -> m Int
eval (Con a) = return a
eval (Div t u) = do
  a <- eval t
  b <- eval u
  return $ div a b




