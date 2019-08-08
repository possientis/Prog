-- overloaded names needs to be defined in separate modules
import Overloading1
import Overloading2


i : Int
i = x       

s : String
s = x


main : IO ()
main = do
  putStrLn $ "i = " ++ show i
  putStrLn $ "s = " ++ show s
