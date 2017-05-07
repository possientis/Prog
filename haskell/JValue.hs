module JValue 
  ( JValue(..)
  ) where

import Data.List (intercalate)
import Data.Char
import Control.Applicative
import Control.Monad

newtype JKeyVal = JKeyVal (String, JValue)

instance Show JKeyVal where
  show (JKeyVal (k,v)) = (show k) ++ ": " ++ (serialize v) 

data JValue = JString String
            | JNumber Double
            | JBool Bool
            | JNull
            | JObject [JKeyVal]
            | JArray  [JValue]

instance Show JValue where show = serialize

serialize :: JValue -> String
serialize (JString s)   = show s
serialize (JNumber n)   = show n
serialize (JBool True)  = "true" 
serialize (JBool False) = "false" 
serialize (JNull)       = "null"
serialize (JObject o)   = "{" ++ (intercalate ", " $ map show o) ++ "}"
serialize (JArray a)    = "[" ++ (intercalate ", " $ map serialize a) ++ "]"



object1 = JObject [JKeyVal ("foo",JNumber 1),   JKeyVal ("bar", JBool False)]
object2 = JObject [JKeyVal ("foo",JNumber 3),   JKeyVal ("bar", JBool True)]
object3 = JObject [JKeyVal ("foo",JNumber 4.5), JKeyVal ("bar", JBool True)]
object4 = JArray [object1, object2, object3]

data Parser a = Parser { run :: String -> [(a, String)] }

instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure  = return
  (<*>) = ap

instance Monad Parser where
  return a  = Parser (\cs -> [(a,cs)])
  m >>= f   = Parser (\cs -> concat [ run (f a) cs' | (a, cs') <- run m cs ]) 

nullParser :: Parser String
nullParser = Parser f where
  f cs = [("",cs)]

parser :: (Char -> Bool) -> Parser String
parser p = Parser f where
  f []      = []
  f (c:cs)  = if p c then [([c],cs)] else []

item :: Parser String           -- "."
item = parser $ const True

char :: Char -> Parser String   -- "c"
char c = parser (== c)

digit :: Parser String          -- "[0-9]"
digit = parser isDigit 

combine :: Parser a -> Parser b -> Parser (a, b)
combine par1 par2 = do
  a <- par1
  b <- par2
  return (a,b)

(<&&>) :: Parser String -> Parser String -> Parser String
(<&&>) par1 par2 = liftM (\(x,y) -> x++y) (combine par1 par2)

(<||>) :: Parser a -> Parser a -> Parser a
(<||>) par1 par2 = Parser f where
  f cs = run par1 cs ++ run par2 cs

plus :: Parser String -> Parser String
plus par = par <||> (par <&&> plus par)  

plus' :: Parser a -> Parser [a]
plus' par = liftM return par <||> 
            liftM (\(x,y) -> (x:y)) (combine par (plus' par))

star :: Parser String -> Parser String
star par = nullParser <||> plus par

star' :: Parser String -> Parser [String]
star' par = liftM return nullParser <||> plus' par

stringToInteger :: String -> Integer
stringToInteger cs = go cs 0 False where
  go []     acc False = acc
  go []     acc True  = -acc
  go (c:cs) acc sign = 
    if isDigit c
      then go cs (10*acc + (toInteger $ digitToInt c)) sign
      else go cs acc (not sign)

minlength :: [(a,String)] -> Int
minlength []    = 0 -- should not matter anyway
minlength [(a,cs)] = length cs
minlength ((a,cs):xs) = 
  let len = minlength xs
      l   = length cs
  in  if l < len then l else len


greed :: Parser a -> Parser a
greed par = Parser f where
  f cs = let 
    xs = run par cs 
    len = minlength xs 
    in filter (\(s, cs') -> length cs' == len) xs 

option :: Parser String -> Parser String 
option par = par <||> nullParser

digits = (greed . plus) digit

natural  :: Parser Integer
natural = do
  s <- digits
  return $ stringToInteger s

integer :: Parser Integer
integer = do
  s <- option (char '-') <&&> digits
  return $ stringToInteger s

posDouble :: Parser Double
posDouble = do
  n1 <- natural 
  s1 <- char '.'
  s2 <- digits
  let n = length s2
  let d1 = fromIntegral n1
  let d2 = fromIntegral (stringToInteger s2)
  let d3 = d2 / (fromIntegral (10^n))
  return $ d1 + d3

posNumber :: Parser Double  
posNumber = greed $ posDouble <||> (liftM fromIntegral natural)

number :: Parser Double
number = do
  s1 <- option (char '-')
  d1 <- posNumber
  if s1 == "-" 
    then return (-d1) 
    else return d1
  
jnumber :: Parser JValue
jnumber = liftM JNumber number 

match :: String -> Parser String
match [] = nullParser 
match (c:cs) = char c <&&> match cs

bool :: Parser Bool
bool  = liftM (\s -> if s == "true" then True else False) $
  match "true" <||> match "false"

jbool :: Parser JValue
jbool = liftM JBool bool

jnull :: Parser JValue
jnull = liftM (const JNull) (match "null")

string :: Parser String
string = do
  s1 <- char '\"'
  s2 <- star (parser (/= '\"')) 
  s3 <- char '\"'
  return s2

jstring :: Parser JValue
jstring = liftM JString string

jkeyval :: Parser JKeyVal
jkeyval = do
  j1 <- string
  s1 <- match ": "
  j2 <- jvalue
  return $ JKeyVal (j1, j2)

jarray :: Parser JValue
jarray = undefined

jobject :: Parser JValue
jobject = undefined


jvalue :: Parser JValue
jvalue = jnumber <||> jbool <||> jnull <||> jstring 
 


main = do 
  print object1
  print object2
  print object3
  print object4
  print $ run jnumber "-4.576abcdef"
  print $ run jbool "trueabcdef"
  print $ run jbool "falseabcdef"
  print $ run jnull "nullabcdef"
  print $ run string "\"this is a string\"abcdef"
  print $ run jkeyval "\"foo\": 1.0abcdef"
  print $ run ((greed . plus') digit) "1234abcdef"







