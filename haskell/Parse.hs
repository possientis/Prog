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


-- identity parse does not affect ParseState and simply returns its argument
identity :: a -> Parse a
identity a = Parse (\s -> Right (a,s))

parse :: Parse a -> L.ByteString -> Either String a
parse parser initState 
  = case runParse parser (ParseState initState 0) of
    Left err          -> Left err
    Right (result, _) -> Right result

modifyOffset :: ParseState -> Int64 -> ParseState
modifyOffset initState newOffset 
  = initState { offset = newOffset } -- creates new ParseState identical to 
                                     -- initState, but with modified offset

before = ParseState (L8.pack "foo") 0
after  = modifyOffset before 3






