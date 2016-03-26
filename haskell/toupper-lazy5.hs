import Data.Char(toUpper)

main = interact (map toUpper . (++) "Your data in uppercase is:\n\n")
