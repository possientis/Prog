data Category object arrow = Category { source :: arrow -> object,
                                        target :: arrow -> object,
                                        ide     :: object-> arrow,
                                        compose:: arrow -> arrow -> arrow}
s :: String -> Char
s _ = 'a'

t :: String -> Char
t _ = 'b'

i :: Char -> String
i 'a' = "String"

comp :: String -> String -> String
comp f g = f ++ g

c = Category s t i comp 

s1 = source c "wwrddff"
t1 = target c "jhfjhfjak"
a1 = ide c 'a'
a2 = compose c "abc" "def"


