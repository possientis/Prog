import Queue

start :: IO ()
start = putStrLn "Queue: starting unit test"

end :: IO ()
end = putStrLn "Queue: unit test complete"

main = start >> test0 >> test1 >> end

-- test0 : checking initial state
a0 :: Queue a
a0 = empty
test0 :: IO ()
test0 = case isEmpty a0 of
  True  -> return ()
  False -> putStrLn "Queue: unit-test 0 failing"

-- test1 : adding one element to queue
a1 = push a0 [1,2]
b1 = push a0 3
testa1 = case isEmpty a1 of
  False  -> return ()
  True -> putStrLn "Queue: unit-test 1 failing"
testb1 = case isEmpty b1 of
  False  -> return ()
  True -> putStrLn "Queue: unit-test 1 failing"
test1 = testa1 >> testb1




