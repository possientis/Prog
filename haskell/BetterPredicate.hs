import Control.Monad (filterM)
import System.Directory (Permissions(..), getModificationTime, getPermissions)
import Data.Time.Clock
import System.FilePath (takeExtension)
import Control.Exception (bracket, handle, SomeException)
import System.IO (IOMode(..), hClose, hFileSize, openFile)

-- the function we wrote earlier
import RecursiveContents (getRecursiveContents)

type Predicate  =   FilePath      -- path to directory entry
                ->  Permissions   -- permissions
                ->  Maybe Integer -- file size (nothing if not file)
                ->  UTCTime 
                ->  Bool   


betterFind :: Predicate -> FilePath -> IO [FilePath]
betterFind p path = getRecursiveContents path >>= filterM check
  where check name = do
          perms     <- getPermissions name
          size      <- getFileSize name
          modified  <- getModificationTime name
          return (p name perms size modified)
               
-- basic, but will throw exception on non-existent file, or pipes etc
simpleFileSize :: FilePath -> IO Integer
simpleFileSize path = do
  h <- openFile path ReadMode
  size <- hFileSize h
  hClose h
  return size


ignore :: SomeException -> IO (Maybe Integer)
ignore = const(return Nothing)

-- better as it throws no exception. However, still unsatisfactory
-- as hFileSize will throw on a pipe (say) and exception handler
-- will be called without any 'finally' clause releasing the ressource.
-- Hence on a big search involving many 'files' for which hFileSize 
-- will fail, we could quickly exhaust linux limit on the number
-- of open file descriptors,
saferFileSize :: FilePath -> IO (Maybe Integer)
saferFileSize path = handle ignore $ do
  h <- openFile path ReadMode
  size <- hFileSize h
  hClose h
  return (Just size)

-- Exception handling with a 'finally' clause to make sure
-- resource gets released. Using the 'bracket' function
-- bracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
-- first argument: the 'acquire' action
-- second argument: the 'release' action
-- third argument: the 'use' action
-- bracket ensure that release is called, whether or not 'use' throws

getFileSize :: FilePath -> IO (Maybe Integer)
getFileSize path = handle ignore $
  bracket (openFile path ReadMode) hClose $ \h -> do
    size <- hFileSize h
    return (Just size)

type InfoP a  = FilePath
              -> Permissions
              -> Maybe Integer
              -> UTCTime
              -> a

pathP :: InfoP FilePath -- otherwise compiler would infer very general type
pathP path _ _ _ = path

sizeP :: InfoP Integer
sizeP _ _ (Just size) _ = size
sizeP _ _ Nothing     _ = -1


equalP :: (Eq a) => InfoP a -> a -> InfoP Bool
equalP f k = \w x y z -> f w x y z == k 

equalP' :: (Eq a) => InfoP a -> a -> InfoP Bool
equalP' f k w x y z = f w x y z == k 



liftP :: (a -> b -> c) -> InfoP a -> b -> InfoP c
liftP q f k w x y z = (f w x y z) `q` k

-- Currying makes it even more important to think about order 
-- of arguments when designing APIs
greaterP, lesserP :: (Ord a) => InfoP a -> a -> InfoP Bool
greaterP = liftP (>)  -- conciseness achieved thanks to careful 
lesserP  = liftP (<)  -- choice of argument order

simpleAndP :: InfoP Bool -> InfoP Bool -> InfoP Bool
simpleAndP f g w x y z = f w x y z && g w x y z

liftP2 :: (a -> b -> c) -> InfoP a -> InfoP b -> InfoP c
liftP2 op f g w x y z = f w x y z `op` g w x y z

andP  = liftP2 (&&)
orP   = liftP2 (||)

constP :: a -> InfoP a
constP k _ _ _ _ = k 

liftP' op f k = liftP2 op f (constP k)

liftPath :: (FilePath -> a) -> InfoP a
liftPath f w _ _ _ = f w 

myTest path _ (Just size) _ =
  takeExtension path == ".cpp" && size < 512
myTest path _ _ _ = False

myTest2 = (liftPath takeExtension `equalP` ".cpp") `andP`
          (sizeP `lesserP` 512)
-- by default, infix operators are 'infixl 9' that is 
-- they are left associative at the highest precedence level ...
(==?) = equalP
(&&?) = andP
(<?)  = lesserP 

-- which means that parantheses are absolutely required here
-- (at least those around 'sizeP < 512' )
myTest3 = (liftPath takeExtension ==? ".cpp") &&? (sizeP <? 512)

-- on ghci , check :i == , :i && and :i < so as to replicate those settings:
infix 4 ==? -- level 4 priority
infix 3 &&? -- now ==? will bind more strongly than &&?
infix 4 <?  -- so we can redefine ur predicate without parentheses:

myTest4 = liftPath takeExtension ==? ".cpp" &&? sizeP <? 512

-- TODO: fix ${HOME} issue
main = do
  paths <- betterFind myTest4 "${HOME}/Prog/"
  putStrLn (show paths)





