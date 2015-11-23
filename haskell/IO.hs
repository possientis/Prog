import Control.Monad
import System.Directory
import Data.List
import System.IO

-- done is neutral element of binary operator (>>) :: IO() -> IO () -> IO ()
-- (>>) is associative
done :: IO ()
done = return ()

-- a simple procedure taking no argument. type is IO ()
proc1 = putChar 'a' >> putStr "bcd" >> putStrLn "efg" >> done
-- attempting to redefine putStr
proc2 :: String -> IO ()
proc2 [] = done
proc2 (x:xs) = putChar x >> proc2 xs

-- more conceisely
proc3 :: String -> IO()
proc3 xs = foldr (>>) done (map putChar xs)

-- even more concisely
proc4 :: String -> IO()
proc4 xs = ((foldr (>>) done) . (map putChar)) xs

-- even more concisely
proc5 :: String -> IO()
proc5 = (foldr (>>) done) . (map putChar)

-- no brackets needed
proc6 :: String -> IO ()
proc6 = foldr (>>) done . map putChar

proc7 = getChar >>= \x -> putChar x

-- redefining getLine -wowowowowow
proc8 :: IO String
proc8 = getChar >>= \x ->
        if x == '\n' then 
          return []
        else 
          proc8 >>= \xs ->
          return (x:xs)
        
-- same code with 'do' notation
proc8' :: IO String
proc8' =  do {
            x <- getChar;
            if x == '\n' then
              return []
            else do {
              xs <- getLine;
              return (x:xs)
            }
           }
-- note that (>>) is a particular case of (>>=)
-- m >> n = m >>= \x ->  n
(££) :: IO () -> IO () -> IO ()
m ££ n = m >>= \x ->  n -- x can only be ()

-- let us redefine putStr with (££)
proc9 :: String -> IO ()
proc9 = foldr (££) done . map putChar


echo :: IO ()
echo = getLine >>= \line ->
  if line == "" then
    return ()
  else
    putStrLn line >>
    echo

-- same with do notation
echo' :: IO ()
echo' = do {
            line <- getLine;
            if line == "" then
              return ()
            else do {
              putStrLn line;
              echo
            }
            }
-- either evaluate 'main' from ghci or compile and run program
main :: IO ()
main = proc7




