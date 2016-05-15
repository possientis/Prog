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

----- discard ---
modifyOffset :: ParseState -> Int64 -> ParseState
modifyOffset initState newOffset 
  = initState { offset = newOffset } -- creates new ParseState identical to 
-----------------

-- 'state { offset = x }' syntactic sugar for 'ParseState (string state) x'
modifyOffset' :: Int64 -> Parse ()
modifyOffset' newOffset = Parse (\state -> Right ((), state { offset = newOffset })) 


getState :: Parse ParseState
getState = Parse (\state -> Right (state, state))

--- discard ------
identity :: a -> Parse a
identity a = Parse (\s -> Right (a,s))
-------------------

bail :: String -> Parse a
bail err  = Parse (\state -> Left 
              ("byte offset " ++ show (offset state) ++ ": " ++ err))

putState :: ParseState -> Parse ()
putState newState = Parse (\state -> Right((), newState))


parseByte' :: Parse Word8
parseByte' = do
  state <- getState
  case L.uncons (string state) of -- L.uncons :: L.ByteString -> Maybe (Word8, L.ByteString)
    Nothing                 -> bail "no more input"
    Just (byte, remainder)  -> do 
      putState newState
      return byte where
        newState  = state { string = remainder, offset = newOffset }
        newOffset = offset state + 1


-------- discard ----------
parseByte :: Parse Word8
parseByte =
  getState ==> \initState ->
  case L.uncons (string initState) of
    Nothing               -> bail "no more input"
    Just (byte,remainder) ->
        putState newState ==> \_ -> identity byte
      where newState = initState {  string = remainder,
                                    offset = newOffset }
            newOffset = offset initState + 1
----------------------------

----------- discard ------------------------------
(==>) :: Parse a -> (a -> Parse b) -> Parse b
parser ==> func = Parse chained
  where chained state = 
          case run parser state of
            Left errMessage           -> Left errMessage
            Right (result, newState)  -> run (func result) newState 
---------------------------------------------------------

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

w2c :: Word8 -> Char
w2c = chr . fromIntegral

parseChar :: Parse Char
parseChar = w2c <$> parseByte

test13 = parse parseChar (L8.pack "hello")  -- Right 'h'

test14 = L8.pack "foobar"
test15 = L8.uncons test14






