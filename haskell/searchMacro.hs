import Data.List

define :: String -> [String]
--define file = foldr step [] (lines file)  -- use composition instead
define = foldr step [] . lines where
  step l defs
    | "#define" `isPrefixOf` l = secondWord l : defs
    | "# define" `isPrefixOf` l = thirdWord l : defs
    | otherwise                = defs
  secondWord = head . tail. words
  thirdWord  = head.tail.tail.words


main = do 
  input <- readFile "/usr/include/stdio.h"
  putStrLn (show (define input))

