import Data.List  -- nub
type Name = String
data Prop = Var Name
          | F
          | T
          | Not Prop
          | Prop :|: Prop
          | Prop :&: Prop
          deriving (Eq, Ord, Show)

type Names = [Name]
type Env = [(Name,Bool)]

dict = [("a",True),("b",False),("c",False)]
propp = ((Var "a") :|: (Var "b")) :&: (Not (Var "c")) 
propq = ((Var "a") :&: (Not (Var "a"))) :|: ((Var "b") :&: (Not (Var "b")))

lookUp :: Eq a => [(a,b)] -> a -> b
lookUp xys x = the [y | (x',y) <- xys, x == x']
  where the [x] = x

envs :: Names -> [Env]
envs [] = [[]]
envs (x:xs) = [(x,False):e | e <- envs xs] ++
              [(x,True):e | e <- envs xs]

eval :: Env -> Prop -> Bool
eval env (Var s) = lookUp env s
eval env F = False
eval env T = True
eval env (Not x) = not (eval env x)
eval env (x :|: y) = (eval env x) || (eval env y)
eval env (x :&: y) = (eval env x) && (eval env y)

names :: Prop -> Names
names (Var s) = [s]
names F = []
names T = []
names (Not x) = names x
names (x :|: y) = nub ((names x) ++ (names y))  -- nub -> no duplicate
names (x :&: y) = nub ((names x) ++ (names y))

satisfiable :: Prop -> Bool
satisfiable p = or [eval e p | e <- envs (names p)]


