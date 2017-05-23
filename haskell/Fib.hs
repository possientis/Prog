import Identity

type M = Id

my_fib :: Integer -> M Integer
my_fib = my_fib_acc 0 1

my_fib_acc :: Integer -> Integer -> Integer -> M Integer
my_fib_acc  _   fn1 1     = return fn1
my_fib_acc  fn2 _   0     = return fn2
my_fib_acc  fn1 fn2 n_rem = do
  val <- my_fib_acc fn1 (fn2 + fn1) (n_rem - 1)
  return val  


main = do
  let n = my_fib 5
  print $ runIdentity n
  
