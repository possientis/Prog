import Set

testSet :: (Show a, Eq a, Ord a, ISet a) => a -> IO ()
testSet empty = 
  do 
  putStrLn "Set: start of unit testing"
  -- set, inc, ==
  if zero   /= empty      then putStrLn "unit test 1.0 failing"   else return ()
  if one    /= inc empty  then putStrLn "unit test 1.1 failing"   else return ()
  if two    /= inc one    then putStrLn "unit test 1.2 failing"   else return ()
  if three  /= inc two    then putStrLn "unit test 1.3 failing"   else return ()
  if four   /= inc three  then putStrLn "unit test 1.4 failing"   else return ()
  if five   /= inc four   then putStrLn "unit test 1.5 failing"   else return ()
  if six    /= inc five   then putStrLn "unit test 1.6 failing"   else return ()
  if seven  /= inc six    then putStrLn "unit test 1.7 failing"   else return ()
  if eight  /= inc seven  then putStrLn "unit test 1.8 failing"   else return ()
  if nine   /= inc eight  then putStrLn "unit test 1.9 failing"   else return ()
  -- empty
  if belong zero  empty   then putStrLn "unit test 2.0 failing"   else return ()
  if belong one   empty   then putStrLn "unit test 2.1 failing"   else return ()
  if belong two   empty   then putStrLn "unit test 2.2 failing"   else return ()
  if belong three empty   then putStrLn "unit test 2.3 failing"   else return ()
  if belong four  empty   then putStrLn "unit test 2.4 failing"   else return ()
  if belong five  empty   then putStrLn "unit test 2.5 failing"   else return ()
  if belong six   empty   then putStrLn "unit test 2.6 failing"   else return ()
  if belong seven empty   then putStrLn "unit test 2.7 failing"   else return ()
  if belong eight empty   then putStrLn "unit test 2.8 failing"   else return ()
  if belong nine  empty   then putStrLn "unit test 2.9 failing"   else return ()
  -- singleton
  if belong zero  szero   then return () else putStrLn "unit test 3.0 failing"
  if belong one   sone    then return () else putStrLn "unit test 3.1 failing"
  if belong two   stwo    then return () else putStrLn "unit test 3.2 failing"
  if belong three sthree  then return () else putStrLn "unit test 3.3 failing"
  if belong four  sfour   then return () else putStrLn "unit test 3.4 failing"
  if belong five  sfive   then return () else putStrLn "unit test 3.5 failing"
  if belong six   ssix    then return () else putStrLn "unit test 3.6 failing"
  if belong seven sseven  then return () else putStrLn "unit test 3.7 failing"
  if belong eight seight  then return () else putStrLn "unit test 3.8 failing"
  if belong nine  snine   then return () else putStrLn "unit test 3.9 failing"

  putStrLn "Set: end of unit testing"
  where
    zero    = set 0; one   = set 1; two   = set 2; three = set 3; four  = set 4
    five    = set 5; six   = set 6; seven = set 7; eight = set 8; nine  = set 9
    szero   = singleton zero
    sone    = singleton one
    stwo    = singleton two
    sthree  = singleton three
    sfour   = singleton four
    sfive   = singleton five
    ssix    = singleton six
    sseven  = singleton seven
    seight  = singleton eight
    snine   = singleton nine



main = testSet (empty::Set)
