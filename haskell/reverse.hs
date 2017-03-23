-- reverse is a fold

import Prelude hiding (reverse)

reverse :: [a] -> [a]
reverse = foldl (\xs x -> x:xs) []


