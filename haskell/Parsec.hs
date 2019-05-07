{-# LANGUAGE TypeSynonymInstances   #-}

module  Parsec
    (   Parser 
    ,   bind_
    ,   char
    ,   digit
    ,   letter
    ,   return_
    ,   satisfy
    )   where

import Data.Char

-- need newtype?
type Parser a = String -> Consumed a

data Consumed a = Consumed (Reply a) | Empty (Reply a)

data Reply a = Ok a String | Error


instance Functor Reply where
    fmap _ Error = Error
    fmap f (Ok x s) = Ok (f x) s

instance Functor Consumed where
    fmap f (Consumed r) = Consumed (fmap f r)
    fmap f (Empty r)    = Empty (fmap f r)

type X a = String -> Maybe a

instance Functor X where
    fmap f p = fmap f . p



return_ :: a -> Parser a
return_ x = \input -> Empty (Ok x input)


satisfy :: (Char -> Bool) -> Parser Char
satisfy test = \input -> case input of
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
bind_ p f = \input -> case (p input) of
    Empty reply1 -> 
        case reply1 of
            Ok x rest   -> (f x) rest
            Error       -> Empty Error
    Consumed reply1 -> Consumed (
        case reply1 of 
            Ok x rest -> 
                case (f x) rest of
                    Consumed reply2 -> reply2
                    Empty reply2    -> reply2
            Error -> Error  
        )






