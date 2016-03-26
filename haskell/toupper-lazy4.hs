-- runghc toupper-lazy4.hs < inputfile > outputfile
--
import Data.Char(toUpper)

main = interact (map toUpper)
