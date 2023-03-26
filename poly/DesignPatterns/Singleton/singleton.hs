-- Singleton design pattern

data SingleObject = SingleObject deriving Eq

getInstance :: SingleObject
getInstance = SingleObject

showMessage :: SingleObject -> IO ()
showMessage SingleObject = putStrLn "The single object is alive and well"

main = do
  let object1 = getInstance in
    showMessage object1 >>
    let object2 = getInstance in
      if object1 == object2 
        then putStrLn "The two objects are the same"
        else return ()

