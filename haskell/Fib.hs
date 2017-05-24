import Identity
import PMD

type M = Pmd

my_fib :: Integer -> M Integer
my_fib = my_fib_acc 0 1

my_fib_acc :: Integer -> Integer -> Integer -> M Integer
my_fib_acc  n0 _   0      = return n0
my_fib_acc  _   n1 1      = return n1
my_fib_acc  n0 n1 n       = do
  val <- my_fib_acc n1 (n0 + n1) (n - 1)
  Pmd (val, putStrLn (show n1))


main = do
  let (Pmd (f25,prt)) = my_fib 25
  prt
  putStrLn ("f25 is " ++ show f25)
  
