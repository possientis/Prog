import Data.Proxy
import Data.Typeable

-- typeRep :: Typeable a => proxy a -> TypeRep 
-- 'proxy' is a type variable
-- so you have more flexibility than just passing
-- a value of type 'Proxy a' , you can use a a value
-- of type '[a]'

x1 :: TypeRep
x1 = typeRep [1::Int]   -- Proxy :: Proxy Int 

x2 :: TypeRep 
x2 = typeRep (Proxy :: Proxy Double)

x3 :: TypeRep 
x3 = typeRep (Proxy :: Proxy [Int -> Double])



main :: IO ()
main = do
    putStrLn $ "typeRep for Int: "                  ++ show x1
    putStrLn $ "typeRep for Double: "               ++ show x2
    putStrLn $ "typeRep for [Int -> Double]: "      ++ show x3
