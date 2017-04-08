for :: a -> (a -> Bool) -> (a -> a) -> (a -> IO ()) -> IO ()
for i p f job =
  if (p i)
    then do
      job i
      for (f i) p f job
    else return ()
  
-- for(i = 0 ; i < 10; ++i){ printf("i = %d\n", i); }

main = for 0 (<10) (+1) (\i -> putStrLn $ "i = " ++ (show i))
