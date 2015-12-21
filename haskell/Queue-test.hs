import Queue

main = queueTest

queueTest = do
  putStrLn "Queue: starting unit test"
  -- checking initial state
  if isEmpty a0 then return () else putStrLn "Queue: unit-test 0.0 failing"
  if isEmpty b0 then return () else putStrLn "Queue: unit-test 0.1 failing"
  if peek a0 == Nothing then return () else putStrLn "Queue: unit-test 0.2 failing"
  if peek b0 == Nothing then return () else putStrLn "Queue: unit-test 0.3 failing"
  if toList a0 == [] then return () else putStrLn "Queue: unit-test 0.4 failing"
  if toList b0 == [] then return () else putStrLn "Queue: unit-test 0.5 failing"
  -- after adding one element to the queue
  if not (isEmpty a1) then return () else putStrLn "Queue: unit-test 1.0 failing"
  if not (isEmpty b1) then return () else putStrLn "Queue: unit-test 1.1 failing"
  if peek a1 == Just 3 then return () else putStrLn "Queue: unit-test 1.2 failing"
  if peek b1 == Just "abc" then return ()else putStrLn"Queue: unit-test 1.3 failing"
  if toList a1 == [3] then return () else putStrLn "Queue: unit-test 1.4 failing"
  if toList b1 == ["abc"] then return () else putStrLn"Queue: unit-test 1.5 failing"
  -- after adding two elements to the queue
  if not (isEmpty a2) then return () else putStrLn "Queue: unit-test 2.0 failing"
  if not (isEmpty b2) then return () else putStrLn "Queue: unit-test 2.1 failing"
  if peek a2 == Just 3 then return () else putStrLn "Queue: unit-test 2.2 failing"
  if peek b2 == Just "abc" then return ()else putStrLn"Queue: unit-test 2.3 failing"
  if toList a2 == [3,5] then return () else putStrLn "Queue: unit-test 2.4 failing"
  if toList b2==["abc","def"]then return()else putStrLn"Queue:unit-test 2.5 failing"
  -- after adding three elements to the queue
  if not (isEmpty a3) then return () else putStrLn "Queue: unit-test 3.0 failing"
  if not (isEmpty b3) then return () else putStrLn "Queue: unit-test 3.1 failing"
  if peek a3 == Just 3 then return () else putStrLn "Queue: unit-test 3.2 failing"
  if peek b3 == Just "abc" then return ()else putStrLn"Queue: unit-test 3.3 failing"
  if toList a3 == [3,5,7] then return () else 
    putStrLn "Queue: unit-test 3.4 failing"
  if toList b3 == ["abc","def","ghi"] then return() else 
    putStrLn"Queue:unit-test 3.5 failing"
  -- after removing first element from the queue
  if not (isEmpty a4) then return () else putStrLn "Queue: unit-test 4.0 failing"
  if not (isEmpty b4) then return () else putStrLn "Queue: unit-test 4.1 failing"
  if peek a4 == Just 5 then return () else putStrLn "Queue: unit-test 4.2 failing"
  if peek b4 == Just "def" then return ()else putStrLn"Queue: unit-test 4.3 failing"
  if toList a4 == [5,7] then return () else putStrLn "Queue: unit-test 4.4 failing"
  if toList b4==["def","ghi"]then return()else putStrLn"Queue:unit-test 4.5 failing"
   -- after removing second element from the queue
  if not (isEmpty a5) then return () else putStrLn "Queue: unit-test 5.0 failing"
  if not (isEmpty b5) then return () else putStrLn "Queue: unit-test 5.1 failing"
  if peek a5 == Just 7 then return () else putStrLn "Queue: unit-test 5.2 failing"
  if peek b5 == Just "ghi" then return ()else putStrLn"Queue: unit-test 5.3 failing"
  if toList a5 == [7] then return () else putStrLn "Queue: unit-test 5.4 failing"
  if toList b5==["ghi"] then return()else putStrLn"Queue:unit-test 5.5 failing"
    -- after removing last element from the queue
  if isEmpty a6 then return () else putStrLn "Queue: unit-test 6.0 failing"
  if isEmpty b6 then return () else putStrLn "Queue: unit-test 6.1 failing"
  if peek a6 == Nothing then return () else putStrLn "Queue: unit-test 6.2 failing"
  if peek b6 == Nothing then return ()else putStrLn"Queue: unit-test 6.3 failing"
  if toList a6 == [] then return () else putStrLn "Queue: unit-test 6.4 failing"
  if toList b6==[] then return()else putStrLn"Queue:unit-test 6.5 failing"
 
  putStrLn "Queue: unit test complete"


a0 :: Queue Int
b0 :: Queue String
a0 = empty
b0 = empty
a1 = push a0 3
b1 = push b0 "abc"
a2 = push a1 5
b2 = push b1 "def" 
a3 = push a2 7
b3 = push b2 "ghi"
a4 = pop a3
b4 = pop b3
a5 = pop a4
b5 = pop b4
a6 = pop a5
b6 = pop b5





