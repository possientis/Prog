import Data.Map

data ShowDict a = ShowDict { showMethod :: a -> String }


showBool :: Bool -> String
showBool True = "True"
showBool False = "False"

showDictBool :: ShowDict Bool
showDictBool = ShowDict showBool






