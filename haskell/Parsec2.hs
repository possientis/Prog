-- Parsec with error messages
module  Parsec2 
    (   Parser  
    ,   satisfy
    )   where
{-
The restriction to LL(1) makes it much easier for us to generate good error
messages. First of all, the error message should include the position of an error.
The parser input is tupled with the current position – the parser state.
-}

newtype Parser a = Parser { run :: State -> Consumed a }

data State = State String Pos
    deriving Show

type Pos = Integer  -- TODO
nextPos :: Pos -> Char -> Pos
nextPos x _ = x + 1

data Consumed a = Consumed (Reply a) | Empty (Reply a)
    deriving Show

{-
Beside the position, it is very helpful for the user to return the grammar produc-
tions that would have led to correct input at that position. This corresponds to
the first set of that production. During the parsing process, we will dynami-
cally compute first sets for use in error messages. This may seem expensive but
laziness ensures that this only happens when an actual error occurs.
An error message contains a position, the unexpected input and a list of expected
productions – the first set.
-}

data Message = Message Pos String [String]
    deriving Show

{-
To dynamically compute the first set, not only Error replies but also Ok replies
should carry an error message. Within the Ok reply, the message represents the
error that would have occurred if this successful alternative wasn’t taken.
-}

data Reply a = Ok a State Message | Error Message
    deriving Show

{-
The return parser attaches an empty message to the parser reply.
-}

return_ :: a -> Parser a
return_ x = Parser $ \state@(State _ pos) -> 
    Empty (Ok x state (Message pos "" []))


{-
The implementation of the satisfy parser changes more. It updates the parse
position if it succeeds and returns an error message with the current position
and input if it fails.
-}

satisfy :: (Char -> Bool) -> Parser Char
satisfy test = Parser $ \(State input pos) -> 
    case input of 
        (c:cs) | test c -> let newPos   = nextPos pos c
                               newState = State cs newPos
                           in seq newPos 
                                (Consumed 
                                    (Ok c newState 
                                        (Message pos "" [])))
        (c:_)           -> Empty (Error (Message pos [c] []))             
        []              -> Empty (Error (Message pos "end of input" [])) 

{-
Note the use of seq to strictly evaluate the new position. If this is done lazily,
we would introduce a new space leak – the original input is retained since it is
needed to compute the new position at some later time.
-}

{-
The (<|>) combinator computes the dynamic first set by merging the error
messages of two Empty alternatives – regardless of their reply value. Whenever
both alternatives do not consume input, both of them contribute to the possible
causes of failure. Even when the second succeeds, the first alternative should
propagate its error messages into the Ok reply.
-}

(<|>) :: Parser a -> Parser a -> Parser a
(<|>) p q = Parser $ \state -> case (run p state) of 
    Empty (Error msg1)      -> case (run q state) of
        Empty (Error msg2)      -> mergeError msg1 msg2
        Empty (Ok x inp msg2)   -> mergeOk x inp msg1 msg2
        consumed                -> consumed
    Empty (Ok x inp msg1)   -> case (run q state) of
        Empty (Error msg2)  -> mergeOk x inp msg1 msg2
        Empty (Ok _ _ msg2) -> mergeOk x inp msg1 msg2
        consumed            -> consumed
    consumed                -> consumed 




