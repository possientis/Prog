import Data.List  -- nub
import Data.Char
import Parser

type Name = String
data Prop = Var Name
          | F
          | T
          | Not Prop
          | Prop :|: Prop
          | Prop :&: Prop
          deriving (Eq, Ord)

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

instance Show Prop where
  show (Var x)    = x
  show F          = "F"
  show T          = "T"
  show (Not p)    = par ("~" ++ show p)
  show (p :|: q)  = par (show p ++ "|" ++ show q)
  show (p :&: q)  = par (show p ++ "&" ++ show q)

par :: String -> String
par s = "(" ++ s ++ ")"


propP :: Parser Prop
propP = varP `mplus` falseP `mplus` trueP `mplus`
        notP `mplus` orP `mplus` andP

varP :: Parser Prop
varP = spot isLower >>= (\x -> return (Var [x]))

falseP :: Parser Prop
falseP = token 'F' >> return F

trueP :: Parser Prop
trueP = token 'T' >> return T

notP :: Parser Prop
notP = parP (token '~' >> propP >>= (\x -> return (Not x)))

orP :: Parser Prop
orP = parP (propP >>= (\p -> token '|' >>  propP >>= (\q -> return (p:|:q))))

andP :: Parser Prop
andP = parP (propP >>= (\p -> token '&' >>  propP >>= (\q -> return (p:&:q))))


parP :: Parser Prop -> Parser Prop
parP p = token '(' >> p >>= (\x -> token ')' >> return x)



