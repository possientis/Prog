data Term = Con Int | Div Term Term

answer, err:: Term
answer = (Div (Div (Div (Div (Con 1972) (Con 2)) (Con 23)) (Con 7)) (Div (Con 10) (Con 5)))
err = (Div (Con 1) (Con 0))

showTerm :: Term -> String
showTerm (Con a) = show a
showTerm (Div a b) = "("++(showTerm a) ++ " div " ++ (showTerm b)++")"

line :: Term -> Int -> String
line t a ="eval("++showTerm t++") <= "++show a++"\n"

---------------------
type M0 a = a

unit0 :: a -> M0 a
unit0 a = a

bind0 :: M0 a -> (a -> M0 b) -> M0 b
bind0 a k = k a

div0 :: Int -> Int -> M0 Int
div0 a b = unit0 (div a b)


eval0 :: Term -> M0 Int
eval0 (Con a) = unit0 a
eval0 (Div t u) = bind0 (eval0 t) (\a -> bind0 (eval0 u) (\b -> div0 a b))

----------------------------
data M1 a = Raise Exception | Return a
type Exception = String

show1 :: (Show a) => M1 a -> String
show1 (Raise e) = e
show1 (Return a) = show a

unit1 :: a -> M1 a
unit1 a = Return a

bind1 :: M1 a -> (a -> M1 b) -> M1 b
bind1 m k = case m of
                Raise e -> Raise e
                Return a -> k a

div1 :: Int -> Int -> M1 Int
div1 a b = if b == 0 then Raise "Exception: division by zero" else Return (div a b)

eval1 :: Term -> M1 Int
eval1 (Con a) = unit1 a
eval1 (Div t u) = bind1 (eval1 t) (\a ->  bind1 (eval1 u) (\b -> div1 a b)) 
--------------------------------
type M2 a = State -> (a,State)
type State = Int

show2 :: (Show a) => M2 a -> String 
show2 m = let (a,i) = m 0 in
          "("++ show a ++ "," ++ show i ++")"

unit2 :: a -> M2 a
unit2 a i = (a,i)

bind2 :: M2 a -> (a -> M2 b) -> M2 b
bind2 m k i = let (a,j) = m i in
              k a j

div2 :: Int -> Int -> M2 Int
div2 a b i =  (div a b, i +1)

eval2 :: Term -> M2 Int
eval2 (Con a) = unit2 a
eval2 (Div t u) = bind2 (eval2 t) (\a -> bind2 (eval2 u) (\b -> div2 a b))
---------------------------------
type M3 a = (a,State)

show3 :: (Show a) => M3 a -> String
show3 m = let (a,i) = m in
          "("++ show a ++ "," ++ show i ++ ")"

unit3 :: a -> M3 a
unit3 a 
            



