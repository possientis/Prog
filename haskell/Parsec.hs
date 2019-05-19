module  Parsec
    (   Parser 
    ,   (<|>)
    ,   char
    ,   digit
    ,   identifier
    ,   letter
    ,   many1
    ,   satisfy
    ,   string
    ,   try
    )   where

import Data.Char
import Control.Monad

newtype Parser a = Parser { run :: String -> Consumed a }

data Consumed a = Consumed (Reply a) | Empty (Reply a)
    deriving Show

data Reply a = Ok a String | Error
    deriving Show

instance Functor Reply where
    fmap _ Error = Error
    fmap f (Ok x s) = Ok (f x) s

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

return_ :: a -> Parser a
return_ x = Parser $ \input -> Empty (Ok x input)


satisfy :: (Char -> Bool) -> Parser Char
satisfy test = Parser $ \input -> case input of
    []                  -> Empty Error
    (c:cs) | test c     -> Consumed (Ok c cs)
    (_:_ ) | otherwise  -> Empty Error

char :: Char -> Parser Char
char c = satisfy (==c)

letter :: Parser Char
letter = satisfy isAlpha


digit :: Parser Char
digit = satisfy isDigit

{-
Due to laziness, a parser (bind_ p f) directly returns with a Consumed construc-
tor if p consumes input. The computation of the final reply value is delayed.
This ‘early’ returning is essential for the efficient behavior of the choice 
combinator.
-}

bind_ :: Parser a -> (a -> Parser b) -> Parser b
bind_ p f = Parser $ \input -> case (run p input) of
    Empty reply1 -> case reply1 of
        Ok x rest   -> run (f x) rest
        Error       -> Empty Error
    Consumed reply1 -> Consumed (
        case reply1 of 
            Ok x rest -> 
                case run (f x) rest of
                    Consumed reply2 -> reply2
                    Empty reply2    -> reply2
            Error -> Error  
        )

{-
An LL(1) choice combinator only looks at its second alternative if the first hasn’t
consumed any input – regardless of the final reply value! Now that the (>>=)
combinator immediately returns a Consumed constructor as soon as some input
has been consumed, the choice combinator can choose an alternative as soon
as some input has been consumed. It no longer holds on to the original input,
fixing the space leak of the previous combinators.

Note that if p succeeds without consuming input the second alternative is fa-
vored if it consumes input. This implements the “longest match” rule.
-}

(<|>) :: Parser a -> Parser a -> Parser a
(<|>) p q = Parser $ \input -> case (run p input) of
    Empty Error  -> (run q input)
    Empty ok     -> case (run q input) of
        Empty _  -> Empty ok
        consumed -> consumed
    consumed     -> consumed 


{-
With the bind and choice combinator we can define almost any parser. Here
are a few useful examples:
-}

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


{-
The (try p) parser behaves exactly like parser p but pretends it hasn’t con-
sumed any input when p fails:
-}

try :: Parser a -> Parser a
try p = Parser $ \input -> case (run p input) of
    Consumed Error  -> Empty Error
    other           -> other

{-
Consider the parser (try p <|> q). Even when parser p fails while consuming
input (Consumed Error), the choice operator will try the alternative q since the
try combinator has changed the Consumed constructor into Empty. Indeed, if
you put try around all parsers you will have an LL(∞) parser again!
-}

{-
In contrast with other libraries, the try combinator is not built into a special
choice combinator. This improves modularity and allows the construction of
lexer libraries that use try on each lexical token. The Parsec library is dis-
tributed with such a library and in practice, try is only needed for grammar
constructions that require lookahead.
-}
