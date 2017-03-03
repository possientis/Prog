data P a  = Belong a a 
          | Bot 
          | Imply (P a) (P a) 
          | Forall a (P a)
  deriving Eq


data Var = Var Int

instance Show Var where
  show (Var 0) = "x"
  show (Var 1) = "y"
  show (Var 2) = "z"
  show (Var 3) = "t"
  show (Var 4) = "s"
  show (Var 5) = "u"
  show (Var 6) = "v"
  show (Var 7) = "w"
  show (Var n) = "x"++ (show (n-8))

-- TODO
instance Show a => Show (P a) where
  show (Belong x y) = (show x) ++ ":" ++ (show y)
  show Bot          = "0"
  show (Imply p (Imply q r))  = (show p) ++ " -> " ++ (show q) ++ "-> " ++ (show r)
  show (Imply (Imply p q) r) = "(" ++ (show p) ++ " -> " ++ (show q) ++ ")" ++ " -> " ++ (show r)
  show (Imply p q) = (show p) ++ " -> " ++ (show q)
  show (Forall x p) = "A"++ (show x) ++ "(" ++ (show p) ++ ")"



x = Var 0
y = Var 1
z = Var 2

(£) :: Var -> Var -> P Var
x£y = Belong x y

bot = Bot :: P Var

(->>) :: P Var -> P Var -> P Var
p ->> q = Imply p q

forall :: Var -> P Var -> P Var
forall x p = Forall x p

p0 = bot                                -- false                          0
p1 = x £ y                              -- x in y                         x:y
p2 = x £ y ->> bot                      -- x in y -> false                x:y -> 0
p3 = forall x (x £ y)                   -- forall x, x in y               Ax(x:y)
p4 = forall x ((x £ y) ->> (x £ z))     -- forall x, x in y -> x in z     Ax(x:y -> x:z)
p5 = forall x (x £ y) ->> (y £ z)       -- (forall x, x in y) -> y in z   Ax(x:y) -> y:z
p6 = (x £ y) ->> ((y £ z) ->> (z £ x))  -- x in y -> y in z -> z in x     x:y -> y:z -> z:x
p7 = ((x £ y) ->> (y £ z)) ->> (z £ x)  -- (x in y -> y in z) -> z in x   (x:y -> y:z) -> z:x
p8 = forall y ((y £ x) ->> bot)         -- forall y, y in x -> false      Ay(y:x -> 0)
p9 = forall x (p8 ->> bot) ->> bot      -- (forall x, (forall y, y in x -> false) -> false) -> false
                                        -- Ax(Ay(y:x -> 0) -> 0) -> 0

main :: IO () 
main = do
  putStrLn $ "p0 = " ++ (show p0)
  putStrLn $ "p1 = " ++ (show p1)
  putStrLn $ "p2 = " ++ (show p2)
  putStrLn $ "p3 = " ++ (show p3)
  putStrLn $ "p4 = " ++ (show p4)
  putStrLn $ "p5 = " ++ (show p5)
  putStrLn $ "p6 = " ++ (show p6)
  putStrLn $ "p7 = " ++ (show p7)
  putStrLn $ "p8 = " ++ (show p8)
  putStrLn $ "p9 = " ++ (show p9)




