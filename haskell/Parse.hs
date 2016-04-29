import qualified Data.ByteString.Lazy.Char8 as L8
import qualified Data.ByteString.Lazy as L
import Data.Int (Int64)

data ParseState = ParseState {
  string :: L.ByteString,
  offset :: Int64
} deriving Show


simpleParse :: ParseState -> (a, ParseState)
simpleParse = undefined


-- gives us ability to return error message
betterParse :: ParseState -> Either String (a, ParseState)
betterParse = undefined

-- single constructor, 'newtype' more efficient than 'data'
-- 'just a compile-time wrapper around a function with no run-time overhead'
-- no to be exported, so we hide implementation details
newtype Parse a = Parse {
  runParse :: ParseState -> Either String (a, ParseState)
}

parse :: Parse a -> L.ByteString -> Either String a
parse parser str
  = case runParse parser (ParseState str 0) of
    Left  err         -> Left err
    Right (result, _) -> Right result

modifyOffset :: ParseState -> Int64 -> ParseState
modifyOffset initState newOffset 
  = initState { offset = newOffset } -- creates new ParseState identical to 

before = ParseState (L8.pack "foo") 0
after  = modifyOffset before 3

-- identity parse does not affect ParseState and simply returns its argument
identity :: a -> Parse a
identity a = Parse (\s -> Right (a,s))

-- dunno which 'import' is required for 'Word8'
--parseByte :: Parse Word8
parseByte =
  getState ==> \initState ->
  case L.uncons (string initState) of
    Nothing               -> bail "no more input"
    Just (byte,remainder) ->
        putState newState ==> \_ -> identity byte
      where newState = initState {  string = remainder,
                                    offset = newOffset }
            newOffset = offset initState + 1

test1 = L8.uncons (L8.pack "foo") -- Just ('f',"oo")

getState :: Parse ParseState
getState = Parse (\s -> Right (s, s))

putState :: ParseState -> Parse ()
putState s = Parse (\_ -> Right((),s))

bail :: String -> Parse a
bail err  = Parse $ \s -> Left $
            "byte offset " ++ show (offset s) ++ ": " ++ err

(==>) :: Parse a -> (a -> Parse b) -> Parse b
parser ==> func = Parse chained
  where chained state = 
          case runParse parser state of
            Left errMessage           -> Left errMessage
            Right (result, newState)  -> runParse (func result) newState 






