-- Parsec with error messages
module  Parsec2 
    (   Parser  
    ,   (<|>)
    ,   char
    ,   digit
    ,   identifier
    ,   letter
    ,   many1
    ,   parse
    ,   satisfy
    ,   string
    ,   try
    )   where

import Data.Char
import Control.Monad

import Prelude hiding (exp)

{-
The restriction to LL(1) makes it much easier for us to generate good error
messages. First of all, the error message should include the position of an error.
The parser input is tupled with the current position – the parser state.
-}

newtype Parser a = Parser { run :: State -> Consumed a }

data State = State String Pos
    deriving Show

parse :: Parser a -> String -> Consumed a
parse p s = run p (State s 0)


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

instance Functor Reply where
    fmap _ (Error msg)  = Error msg
    fmap f (Ok x s msg) = Ok (f x) s msg 

instance Functor Consumed where
    fmap f (Consumed r) = Consumed (fmap f r)
    fmap f (Empty r)    = Empty (fmap f r)

instance Functor Parser where
    fmap f p = Parser $ fmap f . run p

instance Applicative Parser where
    pure  = return
    (<*>) = ap

instance Monad Parser where
    return = return_
    (>>=)  = bind_

{-
The return parser attaches an empty message to the parser reply.
-}

return_ :: a -> Parser a
return_ x = Parser $ \state@(State _ pos) -> 
    Empty (Ok x state (Message pos "" []))


bind_ :: Parser a -> (a -> Parser b) -> Parser b
bind_ p f = Parser $ \state -> case (run p state) of
    Empty reply1 -> case reply1 of
        Ok x state' _   -> run (f x) state'   
        Error msg       -> Empty (Error msg)
    Consumed reply1     -> Consumed (
        case reply1 of
            Ok x state' _ -> 
                case run (f x) state' of
                    Consumed reply2 -> reply2
                    Empty reply2    -> reply2 
            Error msg     -> Error msg
        )
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


mergeOk :: a -> State -> Message -> Message -> Consumed a
mergeOk x inp msg1 msg2 = Empty (Ok x inp (merge msg1 msg2))

mergeError :: Message -> Message -> Consumed a
mergeError msg1 msg2 = Empty (Error (merge msg1 msg2))

merge :: Message -> Message -> Message
merge (Message pos inp exp1) (Message _ _ exp2) = Message pos inp (exp1 ++ exp2) 


{-
The parser (p <?> msg) behaves like parser p but when it fails without consum-
ing input, it sets the expected productions to msg. It is important that it only
does so when no input is consumed since otherwise it wouldn’t be something
that is expected after all:
-}

(<?>) :: Parser a -> String -> Parser a
(<?>) p exp = Parser $ \state -> case (run p state) of
    Empty (Error msg)   -> Empty (Error (expect msg exp))
    Empty (Ok x st msg) -> Empty (Ok x st (expect msg exp))
    other               -> other

expect :: Message -> String -> Message
expect (Message pos inp _) exp = Message pos inp [exp]

char :: Char -> Parser Char
char c = satisfy (==c) <?> (show c)

letter :: Parser Char
letter = satisfy isAlpha <?> "letter"

digit :: Parser Char
digit = satisfy isDigit <?> "digit"



string :: String -> Parser ()
string ""     = return ()
string (c:cs) = do { _ <- char c; string cs } 

many1 :: Parser a -> Parser [a]
many1 p = do
    x  <- p
    xs <- many1 p <|> return []
    return (x:xs)

identifier :: Parser String
identifier = do 
    c  <- letter
    cs <- many1 (letter <|> digit <|> char '_')
    return (c:cs)


try :: Parser a -> Parser a
try p = Parser $ \input -> case (run p input) of
    Consumed (Error msg)  -> Empty (Error msg)
    other                 -> other

