--  L8.pack :: [Char] -> L.ByteString
--  L8.uncons :: L.ByteString -> Maybe (Char, L.ByteString)
--  can work with [Char] instead of [Word8]
import qualified Data.ByteString.Lazy.Char8 as L8 (pack, uncons)


--  L.pack :: [Word8] -> L.ByteString
--  L.uncons :: L.ByteString -> Maybe (Word8, L.ByteString)
import qualified Data.ByteString.Lazy as L
import Data.Int (Int64)
import Control.Applicative -- <$> is alias for infix `fmap`
import Data.Char
import Data.Word

data Greymap = Greymap {
  greyWidth   :: Int,
  greyHeight  :: Int,
  greyMax     :: Word8,
  greyData    :: L.ByteString
} deriving Eq


data ParseState = ParseState {
  string :: L.ByteString,
  offset :: Int64
} deriving Show


-- single constructor, 'newtype' more efficient than 'data'
-- 'just a compile-time wrapper around a function with no run-time overhead'
-- no to be exported, so we hide implementation details
newtype Parse a = Parse { run :: ParseState -> Either String (a, ParseState) }

instance Monad Parse where
  return a  = Parse (\state ->  Right (a, state))
  k >>= f   = Parse (\state ->  case run k state of
                                  Left str            -> Left str
                                  Right (x, newState) -> run (f x) newState) 

parse :: Parse a -> L.ByteString -> Either String a
parse parser str  = case run parser (ParseState str 0) of
                      Left  err         -> Left err
                      Right (result, _) -> Right result

-- 'state { offset = x }' syntactic sugar for 'ParseState (string state) x'
modifyOffset :: Int64 -> Parse ()
modifyOffset newOffset = Parse (\state -> Right ((), state { offset = newOffset })) 


getState :: Parse ParseState
getState = Parse (\state -> Right (state, state))

bail :: String -> Parse a
bail err  = Parse (\state -> Left 
              ("byte offset " ++ show (offset state) ++ ": " ++ err))

putState :: ParseState -> Parse ()
putState newState = Parse (\state -> Right((), newState))


parseByte :: Parse Word8
parseByte = do
  state <- getState
  case L.uncons (string state) of -- L.uncons :: L.ByteString -> Maybe (Word8, L.ByteString)
    Nothing                 -> bail "no more input"
    Just (byte, remainder)  -> do 
      putState newState
      return byte where
        newState  = state { string = remainder, offset = newOffset }
        newOffset = offset state + 1


-- This is the natural definition which turns a monad into a functor.
-- Naively speaking, Let C denote the category of Haskell types where
-- arrows are maps f :: a-> b. Then a monad can be view as a map
-- m :: C0 -> C0 which satisfies certain property (monad laws).
-- A monad is only a map mapping objects of C (the type C0). In order
-- for a monad to become a functor, we need to define its action on the
-- arrows f:: a -> b of the category C, which is what 'fmap' is for.
-- fmap:: (a -> b) -> m a -> m b
-- Now, provided m does indeed satisfies the monad laws, it can be shown
-- the the definition below does indeed define a functor.
instance Functor Parse where
  fmap f parser = parser >>= \result -> return (f result)

--             f
--      a ----------> b
--      |           |
--  ra  |           | rb
--      |           |
--      v           v
--     m a ------> m b
--          fmap f 
--
-- One of the monad laws ensures this diagram commutes.
-- The other two ensures we really have a functor.


test2 = parse parseByte (L8.pack "")          -- Left "byte offset 0: no more input"
test3 = parse (id <$> parseByte) (L8.pack "") -- Left "byte offset 0: no more input"
-- we cannot conclude that (id <$>) is the identity on Parse GHC.Word.Word8
-- we cannot even conclude that they coincide on the particular parser parseByte,
-- but at least we have succesfully checked that the two parsers (id <$> parseByte)
-- parseByte produce the same output on the empty ByteString.

test4 = L8.pack "foo"
test5 = L.head test4 -- 102
test6 = parse parseByte test4           -- Right 102 
test7 = parse (id <$> parseByte) test4  -- Right 102
-- parseByte and (id <$> parseByte) have same output on "foo" ByteString

-- testing composition law for functor
test8 = parse ((chr.fromIntegral) <$> parseByte) test4            -- Right 'f'
test9 = parse (((chr <$>) . (fromIntegral <$>)) parseByte) test4  -- Right 'f'
test10 = parse (chr <$> fromIntegral <$> parseByte) test4         -- Right 'f'    <$> is right associative

test11 = parse ((chr.(+2).fromIntegral) <$> parseByte) test4      -- Right 'h'
test12 = parse (chr <$> ((+2).fromIntegral) <$> parseByte) test4  -- Right 'h'


-- One of the advantages of turning our Parse moand into a functor, is code reuse:
-- we have define parseByte :: Parse Word8 and we have a function:

w2c :: Word8 -> Char
w2c = chr . fromIntegral

-- This gives us an element parseChar :: Parse Char immediately for free:
parseChar :: Parse Char
parseChar = w2c <$> parseByte

test13 = parse parseChar (L8.pack "hello")  -- Right 'h'

-- we have: 
-- getState :: Parse ParseState
-- string   :: ParseState -> L.ByteString
-- L.uncons :: L.ByteString ->  Maybe (Word8, L.ByteString)
-- fst      :: (Word8, L.ByteString) -> Word8
-- fmap fst :: Maybe (Word8, L.ByteString) -> Maybe Word8
-- fmap fst . L.uncons . string :: ParseState -> Maybe Word8
-- Hence:
-- fmap (fmap fst . L.uncons . string) :: Parse ParseState -> Parse (Maybe Word8)
-- (fmap fst . L.uncons . string) <$> getState :: Parse (Maybe Word8)


peekByte :: Parse (Maybe Word8)
peekByte = (fmap fst . L.uncons . string) <$> getState

peekChar :: Parse (Maybe Char)
-- You first lift w2c to the Maybe monad, fmap w2c:: Maybe Word8 -> Maybe Char
-- and then list that to the Parse monad:
peekChar = fmap w2c <$> peekByte


parseWhile :: (Word8 -> Bool) -> Parse [Word8]
parseWhile p = do
  byte <- peekByte
  if fmap p byte == Just True 
    then do
      b <- parseByte
      -- parseByte :: Parse Word8 
      -- b :: Word8
      -- (b:) :: [Word8] -> [Word8]
      -- fmap (b:) :: Parse [Word8] -> Parse [Word8]
      -- parseWhile p :: Parse [Word8]
      -- ==============================================
      -- (b:) <$> parseWhile p :: Parse [Word8]   
      (b:) <$> parseWhile p -- <$> is `fmap`
    else return []


test14 = parseWhile (\x -> w2c x == 'a')
test15 = parse test14 (L8.pack "aaaaabc") -- Right [97,97,97,97,97]

-- f :: Word8 -> a
-- p :: a -> Bool
-- p.f :: Word8 -> Bool
-- parseWhile (p . f) :: Parse [Word8]
-- =====================================================
-- fmap f :: [Word8] -> b for some type b
-- =====================================================
-- fmap f :: [Word8] -> [a]
-- fmap (fmap f) :: Parse [Word8] -> Parse [a]
-- fmap f <$> parseWhile (p . f) :: Parse [a]
-- so the first fmap refers to the [] monad (and functor) 
-- while the second refers to the Parse monad (and functor)
parseWhileWith :: (Word8 -> a) -> (a -> Bool) -> Parse [a]
parseWhileWith f p = fmap f <$> parseWhile (p . f)

parseNat :: Parse Int -- try Integer
parseNat = do 
  digits <- parseWhileWith w2c isDigit
  if null digits
    then bail "no more inputs"
    else let n = read digits
         in if n < 0  -- test failing for overflow it seems
              then bail "integer overflow"
              else return n  

test16 = parse parseNat (L8.pack "24545abc88")  -- 24545
test17 = parse parseNat (L8.pack "567546715475417546154615745654654716751657")  -- Int or Integer ?

skipSpaces :: Parse ()
skipSpaces = do 
  parseWhileWith w2c isSpace 
  return ()

assert :: Bool -> String -> Parse ()
assert True _     = return ()
assert False err  = bail err


parseBytes :: Int -> Parse L.ByteString
parseBytes n = do
  state <- getState
  let n' = fromIntegral n
      (h,t) =  L.splitAt n' (string state)
      state' = state { offset = offset state + L.length h, string = t }
  putState state'
  assert (L.length h == n') "end of input"
  return h 

parseRawPGM  = do
  header <- parseWhileWith w2c notWhite
  skipSpaces
  assert (header == "P5") "invalid raw header"
  width   <- parseNat
  skipSpaces
  height  <- parseNat
  skipSpaces
  maxGrey <- parseByte
  bitmap <- parseBytes (width * height)
  return (Greymap width height maxGrey bitmap)
  where notWhite = (`notElem` " \r\n\t")



  







