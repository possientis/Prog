TupleVect : Nat -> Type -> Type
TupleVect Z a     = ()
TupleVect (S n) a = (a, TupleVect n a)

test1 : TupleVect 4 Nat
test1 = (1,(2,(3,(4,()))))

test2 : TupleVect 4 Nat
test2 = (1,2,3,4,())    -- syntactic sugar


main : IO ()
main = do
  printLn $ test1 == test2  -- True

