import Data.List

data Exp = Lit String | And Exp Exp | Or Exp Exp | Many Exp deriving Show

  
(/-) :: String -> String -> Maybe String
s1 /- s2 = if isPrefixOf s2 s1
            then Just (drop (length s2) s1)
            else Nothing

-- given a regular expression and a string, returns the list
-- of all prefixes of the string which belong to the language
-- defined by the regular expression
parse :: Exp -> Maybe String -> [String]
parse _ Nothing             = []
parse (Lit s0) (Just s)     = if isPrefixOf s0 s then [s0] else []
parse (And r1 r2) (Just s)  = [s1 ++ s2 | s1 <- parse r1 (Just s), 
                                          s2 <- parse r2 (s /- s1)] 
parse (Or r1 r2) (Just s)   = parse r1 (Just s) ++ parse r2 (Just s)
parse (Many r) (Just s)     = "":[s1 ++ s2 | s1 <- parse r (Just s),
                                             s2 <- parse (Many r) (s /- s1),
                                             s1 /= ""] 
test1 = And (Or (Lit "foo") (Lit "foobar")) (Many (Lit "bar"))
test2 = Many (Lit "a")                      

-- all very nice to write code, but no proof of correctness
recognize :: Exp -> String -> Bool
recognize r s = s `elem` (parse r (Just s))

