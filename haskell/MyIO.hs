-- need to understand this code

module MyIO(MyIO, myPutChar, myGetChar, convert) where

type Input = String
type Remainder = String
type Output = String

data MyIO a = MyIO (Input -> (a, Remainder,Output))

apply :: MyIO a -> Input -> (a, Remainder,Output)
apply (MyIO f) inp = f inp

myPutChar :: Char -> MyIO ()
myPutChar c = MyIO (\inp -> ((), inp, [c]))

myGetChar :: MyIO Char
myGetChar = MyIO (\(ch:rem) -> (ch,rem,""))

instance Monad MyIO where
  return x = MyIO (\inp -> (x,inp,""))
  m >>= k = MyIO (\inp ->
            let (x, rem1, out1) = apply m inp in
            let (y, rem2,out2) = apply (k x) rem1 in
            (y, rem2,out1 ++ out2)) 

proc1 = apply (myGetChar >>= \x -> myGetChar >>= \y -> return [x,y]) "abc"
proc2 = apply (myPutChar 'A' >> myPutChar 'B') "def"
proc3 = apply (myGetChar >>= \x -> myPutChar x) "abc"

convert :: MyIO() -> IO()        -- defined in prelude: interact
convert m = interact (\inp ->    -- interact :: (String -> String) -> IO() 
                let (x,rem,out) = apply m inp in
                 out) 

myPutStr :: String -> MyIO()
myPutStr = foldr (>>) (return ()) . map myPutChar

myPutStrLn :: String -> MyIO()
myPutStrLn s = myPutStr s >> myPutChar '\n'


myGetLine :: MyIO String
myGetLine = myGetChar >>= \x ->
            if x == '\n' then
              return []
            else
              myGetLine >>= \xs ->
              return (x:xs)

myEcho :: MyIO ()
myEcho = myGetLine >>= \line ->
         if line == "" then
          return ()
         else
            myPutStrLn line >>
            myEcho
main :: IO ()
main = convert myEcho

