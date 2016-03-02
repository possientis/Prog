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
  -- 
  if belong zero  sfour   then putStrLn "unit test 4.0 failing"   else return ()
  if belong one   sfour   then putStrLn "unit test 4.1 failing"   else return ()
  if belong two   sfour   then putStrLn "unit test 4.2 failing"   else return ()
  if belong three sfour   then putStrLn "unit test 4.3 failing"   else return ()
  if belong five  sfour   then putStrLn "unit test 4.4 failing"   else return ()
  if belong six   sfour   then putStrLn "unit test 4.5 failing"   else return ()
  if belong seven sfour   then putStrLn "unit test 4.6 failing"   else return ()
  if belong eight sfour   then putStrLn "unit test 4.7 failing"   else return ()
  if belong nine  sfour   then putStrLn "unit test 4.8 failing"   else return ()
  -- union: set1 = {0,1,7,4} 
  if belong zero  set1    then return () else putStrLn "unit test 5.0 failing"
  if belong one   set1    then return () else putStrLn "unit test 5.1 failing"
  if belong seven set1    then return () else putStrLn "unit test 5.2 failing"
  if belong four  set1    then return () else putStrLn "unit test 5.3 failing"
  if belong two   set1    then putStrLn "unit test 5.4 failing"   else return ()
  if belong three set1    then putStrLn "unit test 5.5 failing"   else return ()
  if belong five  set1    then putStrLn "unit test 5.6 failing"   else return ()
  if belong six   set1    then putStrLn "unit test 5.7 failing"   else return ()
  if belong eight set1    then putStrLn "unit test 5.8 failing"   else return ()
  if belong nine  set1    then putStrLn "unit test 5.8 failing"   else return ()
  -- subset
  if subset zero  one     then return () else putStrLn "unit test 6.0 failing"
  if subset one   two     then return () else putStrLn "unit test 6.1 failing"
  if subset two   three   then return () else putStrLn "unit test 6.2 failing"
  if subset three four    then return () else putStrLn "unit test 6.3 failing"
  if subset four  five    then return () else putStrLn "unit test 6.4 failing"
  if subset five  six     then return () else putStrLn "unit test 6.5 failing"
  if subset six   seven   then return () else putStrLn "unit test 6.6 failing"
  if subset seven eight   then return () else putStrLn "unit test 6.7 failing"
  if subset eight nine    then return () else putStrLn "unit test 6.8 failing"
  -- 
  if subset zero  zero    then return () else putStrLn "unit test 7.0 failing"
  if subset one   one     then return () else putStrLn "unit test 7.1 failing"
  if subset two   two     then return () else putStrLn "unit test 7.2 failing"
  if subset three three   then return () else putStrLn "unit test 7.3 failing"
  if subset four  four    then return () else putStrLn "unit test 7.4 failing"
  if subset five  five    then return () else putStrLn "unit test 7.5 failing"
  if subset six   six     then return () else putStrLn "unit test 7.6 failing"
  if subset seven seven   then return () else putStrLn "unit test 7.7 failing"
  if subset eight eight   then return () else putStrLn "unit test 7.8 failing"
  if subset nine  nine    then return () else putStrLn "unit test 7.9 failing"
  --
  if subset one   zero    then putStrLn "unit test 8.0 failing"   else return ()
  if subset two   one     then putStrLn "unit test 8.1 failing"   else return ()
  if subset three two     then putStrLn "unit test 8.2 failing"   else return ()
  if subset four  three   then putStrLn "unit test 8.3 failing"   else return ()
  if subset five  four    then putStrLn "unit test 8.4 failing"   else return ()
  if subset six   five    then putStrLn "unit test 8.5 failing"   else return ()
  if subset seven six     then putStrLn "unit test 8.6 failing"   else return ()
  if subset eight seven   then putStrLn "unit test 8.7 failing"   else return ()
  if subset nine  eight   then putStrLn "unit test 8.8 failing"   else return ()
  -- <=
  if zero   <=  one       then return () else putStrLn "unit test 9.0 failing"
  if one    <=  two       then return () else putStrLn "unit test 9.1 failing"
  if two    <=  three     then return () else putStrLn "unit test 9.2 failing"
  if three  <=  four      then return () else putStrLn "unit test 9.3 failing"
  if four   <=  five      then return () else putStrLn "unit test 9.4 failing"
  if five   <=  six       then return () else putStrLn "unit test 9.5 failing"
  if six    <=  seven     then return () else putStrLn "unit test 9.6 failing"
  if seven  <=  eight     then return () else putStrLn "unit test 9.7 failing"
  if eight  <=  nine      then return () else putStrLn "unit test 9.8 failing"
  -- 
  if zero   <=  zero      then return () else putStrLn "unit test 10.0 failing"
  if one    <=  one       then return () else putStrLn "unit test 10.1 failing"
  if two    <=  two       then return () else putStrLn "unit test 10.2 failing"
  if three  <=  three     then return () else putStrLn "unit test 10.3 failing"
  if four   <=  four      then return () else putStrLn "unit test 10.4 failing"
  if five   <=  five      then return () else putStrLn "unit test 10.5 failing"
  if six    <=  six       then return () else putStrLn "unit test 10.6 failing"
  if seven  <=  seven     then return () else putStrLn "unit test 10.7 failing"
  if eight  <=  eight     then return () else putStrLn "unit test 10.8 failing"
  if nine   <=  nine      then return () else putStrLn "unit test 10.9 failing"
  --
  if one    <=  zero      then putStrLn "unit test 11.0 failing"   else return ()
  if two    <=  one       then putStrLn "unit test 11.1 failing"   else return ()
  if three  <=  two       then putStrLn "unit test 11.2 failing"   else return ()
  if four   <=  three     then putStrLn "unit test 11.3 failing"   else return ()
  if five   <=  four      then putStrLn "unit test 11.4 failing"   else return ()
  if six    <=  five      then putStrLn "unit test 11.5 failing"   else return ()
  if seven  <=  six       then putStrLn "unit test 11.6 failing"   else return ()
  if eight  <=  seven     then putStrLn "unit test 11.7 failing"   else return ()
  if nine   <=  eight     then putStrLn "unit test 11.8 failing"   else return ()

  putStrLn "Set: end of unit testing"
  where
    zero    = set 0; one   = set 1; two   = set 2; three = set 3; four  = set 4
    five    = set 5; six   = set 6; seven = set 7; eight = set 8; nine  = set 9
    szero   = singleton zero;   sone    = singleton one
    stwo    = singleton two;    sthree  = singleton three
    sfour   = singleton four;   sfive   = singleton five
    ssix    = singleton six;    sseven  = singleton seven
    seight  = singleton eight;  snine   = singleton nine
    set1    = union (union two (singleton seven)) (singleton four) -- {0,1,7,4}



main = testSet (empty::Set)
