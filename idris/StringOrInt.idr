StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True  = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety four"
getStringOrInt True  = 94

valToString :  (isInt : Bool) 
            -> (case isInt of 
                  False =>  String
                  True  =>  Int
               ) 
            -> String
valToString False x = trim x
valToString True x  = cast x

show : (isInt:Bool) -> StringOrInt isInt -> String
show False x = x
show True  x = show x

main : IO ()
main = do
  putStr "Input a boolean value: "
  s <- getLine 
  let b = if s == "True" then True else False
  putStrLn $ show b $ getStringOrInt b

