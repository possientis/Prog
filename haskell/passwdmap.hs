import Data.List
import qualified Data.Map as Map
import System.IO
import Text.Printf(printf)
import System.Environment(getArgs)
import System.Exit
import Control.Monad(when)


-- The primary piece of data this program will store.
-- It represents the fields in a POSIX /etc/passwd file
data PasswdEntry = PasswdEntry {
  userName :: String,
  password :: String,
  uid :: Integer,
  gid :: Integer,
  gecos :: String,
  homeDir :: String,
  shell :: String}
  deriving (Eq, Ord)

-- Define how we get data to a 'PasswdEntry'
instance Show PasswdEntry where
  show pe = printf "%s:%s:%d:%d:%s:%s:%s"
            (userName pe) (password pe) (uid pe) (gid pe)
            (gecos pe) (homeDir pe) (shell pe)


-- Converting data back out of a 'PasswdEntry'
instance Read PasswdEntry where
  readsPrec _ value =
case split ':' value of
[f1, f2, f3, f4, f5, f6, f7] ->
-- Generate a 'PasswdEntry' the shorthand way:
-- -- using the positional fields. We use 'read' to convert
-- -- the numeric fields to Integers.
-- [(PasswdEntry f1 f2 (read f3) (read f4) f5 f6 f7, [])]
-- x -> error $ "Invalid number of fields in input: " ++ show x

