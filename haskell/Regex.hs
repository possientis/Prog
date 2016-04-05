import Text.Regex.Posix
import qualified Data.ByteString.Char8 as L

bool1 = "my left foot" =~ "foo" :: Bool -- True
bool2 = "my left foot" =~ "bar" :: Bool -- False
bool3 = "my left foot" =~ "(foo|bar)" :: Bool -- True

int1 = "a start called henry" =~ "planet" :: Int  -- 0
int2 = "honorificabilitudinitatibus" =~ "[aeiou]" :: Int -- 13

str1 = "I, B. Ionsonii, uurit a lift'd batch" =~ "(uu|ii)" :: String -- "ii"
str2 = "hi ludi, F. Baconis nati, tuiti orbi" =~ "Shakespeare" :: String -- ""

list1 = "I, B. Ionsonii, uurit a lift'd batch" =~ "(uu|ii)" :: [[String]] -- [["ii","ii"],["uu","uu"]]
list2 = "fooooooooooo" =~ "o" ::[[String]] -- [["o"],["o"],["o"],["o"],["o"],["o"],["o"],["o"],["o"],["o"],["o"]]
list3 = "foo goo bar" =~ "(.)o(.)" :: [[String]] -- [["foo","f","o"],["goo","g","o"]]

list4 = getAllTextMatches $ "I, B. Ionsonii, uurit a lift'd batch" =~ "(uu|ii)" :: [String] -- ["ii","uu"]
list5 = getAllTextMatches $ "hi ludi, F. Baconis nati, tuiti orbi" =~ "Shakespeare" :: [String] -- []

pattern = "(foo[a-z]*bar|quux)"

tuple1 = "before foodiebar after" =~ pattern :: (String,String,String) -- ("before ","foodiebar"," after")
tuple2 = "no match here" =~ pattern :: (String,String,String) -- ("no match here","","")
tuple3 = "before foodiebar after" =~ pattern :: (String,String,String,[String]) -- ("before ","foodiebar"," after",["foodiebar"])

tuple4 = "before foodiebar after" =~ pattern :: (Int,Int) -- (7,9) (position of first match + length) 
tuple5 = "eleemosynary" =~ pattern :: (Int,Int) -- (-1, 0)


bool4 = L.pack "foo" =~ "bar" :: Bool -- False
int3  = "foo" =~ L.pack "bar" :: Int  -- 0
tuple6 = L.pack "foo" =~ L.pack "o" :: (Int,Int)  -- (1,1)

bytes1 = L.pack "good food" =~ ".ood" :: [[L.ByteString]] -- [["good"],["food"]]
-- bytes2 = "good food" =~ ".ood" :: [[L.ByteString]] -- failing coz "good food" is a string
str3 = "good food" =~ ".ood" :: [[String]]  -- [["good"],["food"]] , this works

-- Left hand type (String or ByteString) needs to match return type
-- Right hand type for pattern can be either String or ByteString




