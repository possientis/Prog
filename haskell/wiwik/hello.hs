main :: IO ()
main = putStrLn $ "Hello world!: " ++ show (func 6)


func :: Int -> Int
func n = n + 7

