import Data.Char
-- counts the number of words which start with a capital letter
-- example which illustrates the use of the composition operator (.)
capCount = length.filter (isUpper.head).words

