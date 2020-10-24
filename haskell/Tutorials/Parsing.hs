import Data.List
import Control.Monad        (ap, liftM)
import Control.Applicative  (Alternative (..))

-- Let us consider the following abstract syntax for a very simple language
data Expr
    = ENum Integer
    | EAdd Expr Expr
    | EMul Expr Expr
    deriving (Show, Eq)

-- Example of expressions are as follows:

-- 34                                               -- concrete syntax
exp0 :: Expr
exp0 = ENum 34                                      -- abstract syntax

-- 34 + 12                                          -- concrete syntax
exp1 :: Expr
exp1 = EAdd (ENum 34) (ENum 12)                     -- abstract syntax

-- 34 * 12                                          -- concrete syntax
exp2 :: Expr
exp2 = EMul (ENum 34) (ENum 12)                     -- abstract syntax

-- 56 * (34 + 12)                                   -- concrete syntax
exp3 :: Expr
exp3 = EMul (ENum 56) (EAdd (ENum 34) (ENum 12))    -- abstract syntax

-- The notion of abstract syntax is very important as all the programming is done
-- around it. It would be very difficult and messy to deal with the concrete syntax 
-- directly. For example, the abstract syntax allows to write an interpreter:

eval :: Expr -> Integer
eval (ENum n) = n
eval (EAdd e e') = eval e + eval e'
eval (EMul e e') = eval e * eval e'

-- But of course, a real program needs to read the concrete syntax provided by
-- the user, either directly from the terminal, or from a source file. In fact
-- this very file is written using Haskell's concrete syntax.

-- Enters the notion of PARSING: it is the process of converting the concrete
-- syntax into the abstract syntax, a very important process.

-- On the face of it, parsing appears to be the design of a function:
parse1 :: String -> Expr
parse1 = undefined  -- parse1 "34 + 12" should be e1

-- While this conception of parsing is correct, it is not a good way to approach 
-- the problem, because parsing is the result of processing a string bits by bits,
-- and we want to be able to represent all the intermediate stages of parsing.
-- Hence a better approach would be to aim at writing a function:

parse2 :: String -> (Expr, String)
parse2 = undefined  -- parse2 "34 + 12" could be (ENum 34, "+ 12")

-- This function would return an expression, together with the remainder of the
-- input String which was not processed and remains to be analysed.

-- Note that there is no fundamental difference between (Expr, String) and 
-- (String, Expr). Our choice of order is arbitrary and we could equally have:

parse3 :: String -> (String, Expr)
parse3 = undefined  -- parse3 "34 + 12" could be ("+ 12", ENum 34)

-- However, this does not work either: it is very unlikely that all intermediate
-- stages of parsing will lead to a valid expression of the abstract syntax.
-- In fact, from the string "34 + 12" we could extract the expression "ENum 34",
-- but we are then left with the string "+ 12" from which we would like to consume
-- or process the character '+'. So parse2 "+ 12" should be something like 
-- (???,"12") but we do not have an expression of the abstract syntax to return.

-- As we do not want to return a meaningful expression, we need a parser:
parse4 :: String -> ((),String) -- processes part of input string, returns ()
parse4 = undefined

-- Sometimes we may want our parser to return a simple character, so we need:
parse5 :: String -> (Char, String)
parse5 = undefined

-- or we may want to get an integer:
parse6 :: String -> (Integer, String)
parse6 = undefined

-- So it appears we need different types of parsers depending on what it is we 
-- expect at a given intermediary stage of our parsing.

-- Dealing with all these different types is cumbersome but luckily Haskell has
-- polymorphism: this allows us to express all these different types as one.

parse7 :: String -> (a, String) -- 'a' is called a 'type variable'
parse7 = undefined

-- However, this is still not good enough: suppose you expect an integer and
-- you are parsing the string "34 + 12". Let us assume our parser is clever
-- enough and can discard whitespaces so our input string is really "34+12".
-- We expect the result of the intermediate parse to return (34,"+12"), but
-- 3 is also a valid integer. So the result (3,"4+12") is also a valid parse.
-- If we simply ask our parser "give me an integer", the parser cannot be 
-- blamed for returning (3,"4+12"). So we see that in some situations, parsing
-- may lead to more than one possible answer. So our parsers should be allowed
-- to return a list of answers, rather than a single answer:

parse8 :: String -> [(a, String)]
parse8 = undefined

-- The polymorphic type: String -> [(a, String)] seems to be the right type
-- to consider, and we should give it a name. One solution is a type synonym:

type Parser1 a = String -> [(a, String)]

-- So now we do not need to write 'String -> [(a, String)]' everywhere and 
-- we can simply write 'Parser1 a' which not only is shorter, but also more
-- readable with a meaningful name declaring the intent of the programmer.

-- Note that a type synonym is not always the preferred approach, because all
-- synonyms are considered to be the same type by Haskell, and if you happen
-- to mix them up, there will be no typing error to warn you. 

-- A more type-safe solution is to use the 'data' keyword
data Parser2 a = MkParser2 (String -> [(a, String)])

-- Here 'Parser2' is a type constructor (it constructs a new type from a type
-- argument 'a') while MkParser2 is called the 'data constructor' (it creates
-- values of type 'Parser2 a' from some argument f :: String -> [(a, String)]

-- In Haskell, the namespaces for types (and type constructors) and for values
-- (and data constructors) are separate, and people usually prefer to use the 
-- same name for both the type constructor and the data constructor.

data Parser3 a = Parser3 (String -> [(a, String)])

-- As you can see, the same name 'Parser3' is used for both the type constructor
-- and data constructor without creating a conflict in Haskell.

-- The type 'Parser3 a' has only one data constructor, unlike our abstract syntax 
-- type 'Expr' which has three. While it is perfectly possible to use the 'data'
-- keyword to define a new type with a single constructor, most people prefer
-- using the 'newtype' keyword:

newtype Parser4 a = Parser4 (String -> [(a, String)])

-- Unlike type synonyms which are regarded as the same type by Haskell, declaring
-- a newtype will ensure it cannot be mixed up with 'String -> [(a, String)]'.
-- Unlike types declared with 'data', a 'newtype' will be as efficient at runtime
-- as the underlying type String -> [(a, String)]. Hence for types which a unique
-- type constructor, using the keyword 'newtype' brings the best of both worlds:
-- total type safety without runtime cost.

-- It is very common when declaring a newtype to use the syntax:

newtype Parser a = Parser { runParser :: String -> [(a, String)] }

-- This syntax allows you to declare both the type and its accessor, i.e.
-- runParser :: Parser a -> String -> [(a, String)] 
-- which is a function extracting the underlying function used to create
-- a value of type 'Parser a'.

-- So if we had a parser for exressions:
parser1 :: Parser Expr              -- parser returning an 'Expr'
parser1 = undefined                 -- we still need to write such a parser

-- We could 'run' this parser on the string "34 + 12"
ex1 :: [(Expr, String)]
ex1 = runParser parser1 "34 + 12"

-- and hopefully obtain the list with a single result: 
--  [(EAdd (ENum 34) (ENum 12), "")]. 
--
-- Note that when declaring our type 'Parser a', we could have used another name 
-- for the accessor 'runParser', but this name turns out to be a good choice.
-- 
-- Note that a parse which yields a singleton list is good: there is only one
-- possible result and the parse is unambiguous.
--
-- A parse which yields the empty string "" is also good: there is no more input
-- to process and the parse was in fact successful.

-- Another advantage of declaring our type 'Parser a' is that it allows us to
-- free our brain from remembering the details of what a parser really is: a
-- value of type 'Parser a' (aka a parser of type 'a') is something which you can
-- run against a string using 'runParser' to obtain a value of type 'a' together 
-- with the remainder of the input string which needs to be processed.

-- Now that we have settled our Parser type, we need to start writing parsers.

-- One parser which is bound to be useful is a Char parser which returns
-- a Char if it satifies a given condition. So given a predicate function
-- p :: Char -> Bool, the parser will consume the first character c and return
-- it if the condition (p c) is True, otherwise will fail to return anything.

sat :: (Char -> Bool) -> Parser Char
sat p = Parser f where
    f [] = []           -- parser has no result at all on an empty input string 
    f (c:cs) = if p c
        then [(c,cs)]   -- returns unique solution with character c remainder cs 
        else []         -- cannot return a single successful parse. 

-- A parser which will always succeed on an non-empty input is a Char parser
-- returning the first character of the input.

item :: Parser Char
item = sat (const True) -- the condition is always True

-- run ghci on the terminal and type 'ex2' to check its value
ex2 :: [(Char, String)]
ex2 = runParser item "34 + 12"          -- [('3',"4 + 12")] , so far so good

-- Another Char parser of interest is a parser expecting a specific character,
-- and which returns this character if found, and otherwise fails.

char :: Char -> Parser Char
char c = sat (== c)

ex3 :: [(Char, String)]
ex3 = runParser (char '+') "34 + 12"    -- [] parser has failed to find anything

ex4 :: [(Char, String)]
ex4 = runParser (char '+') "+ 12"       -- [('+'," 12")] , success one parse

-- It is usually the case that one is not able to predict exactly what
-- the remaining input string should contain at a given stage of parsing.
-- For example, you could be expecting an operator without knowing whether
-- it is '+' or '*'. You want to be able to try a given parser without 
-- triggering an overall failure of the parse. So suppose your have two
-- parsers p1 and p2 both of type Parser a. You want to be able to create
-- a new parser which will collect all the successful results from both p1
-- and p2. So if one parser is successful, you will not end up empty-handed.

parseOr :: Parser a -> Parser a -> Parser a
parseOr p1 p2 = Parser f where
    f s = runParser p1 s ++ runParser p2 s

-- This allows us to create a parser for an arithmetic operator
op :: Parser Char
op = parseOr (char '+') (char '*')

ex5 :: [(Char, String)]
ex5 = runParser op "+ 12"               -- [('+'," 12")], this works

ex6 :: [(Char, String)]
ex6 = runParser op "* 12"               -- [('*'," 12")], this works too

-- The ability to try out more than one parser allows us to define another
-- very useful Char parser, which will look for a character in a given list.

range :: [Char] -> Parser Char
range []        = error "range: empty list"
range [c]       = char c    -- only one possible character in the list
range (c:cs)    = parseOr (char c) (range cs)

-- So the operator parser could have been defined as follows:
op' :: Parser Char
op' = range "+*"    -- "+*" is the same as ['+','*'], String = [Char]

ex7 :: [(Char, String)]
ex7 = runParser op' "+ 12"              -- [('+'," 12")], this works

ex8 :: [(Char, String)]
ex8 = runParser op' "* 12"              -- [('*'," 12")], this works too

-- We are now in a position to define a Char parser which expects a digit
digit :: Parser Char
digit = range "0123456789"

ex9 :: [(Char, String)]
ex9 = runParser digit "34 + 12"         -- [('3',"4 + 12")], one successful parse     

ex10 :: [(Char, String)]
ex10 = runParser digit "+ 12"           -- [], no successful parse  

-- So now that we can create a parser which accepts a single digit, can 
-- we create a parser which accepts two digits? More generally, given two 
-- parsers p1 and p2 of type 'a', can we create a parser of type 'a' which
-- will get all the results obtained from p1, and then process each result
-- with the parser p2, to obtain more results? This is about combining parsers:

combine1 :: Parser a -> Parser a -> Parser a
combine1 = undefined

-- However, coming to think of it, there is no reason to insist on the two
-- parsers having the same type. We could run a first parser on the input 
-- string to obtain results of type 'a' (and some remainder string), and 
-- then run a second  parser of type 'b' on the remainder string of each result.

combine2 :: Parser a -> Parser b -> Parser b
combine2 = undefined

-- Unfortunately, this will not work for us: suppose we are looking to parse 
-- two successive digits. What should the result be? We want a final parser 
-- that gives the two digits it found, not simply the last one. So we want
-- a parser which returns a list of Char, not just a single Char. So our 
-- second parser should be of type [Char] or (Char,Char). However, it should 
-- also return the digit which was found from running the first parser.
-- So the result of our second parser should depend on the outcome of the
-- first parser. In other words, we cannot have the same second parser 
-- across the board, we need to make the second parser depend on the result
-- of the first. So let us try the following signature instead:

combine :: Parser a -> (a -> Parser b) -> Parser b

-- We are hoping this signature will do. It allows us to have a different 
-- second parser, depending on the result of type 'a' obtained from the
-- first parser. We can try and implement this parser as follows:

combine p1 f2 = Parser f where
          -- get all the results from running the first parser p1 on the string s
    f s = let xs = runParser p1 s in 
          -- For each result (x,t), run the parser (f2 x) on the remainder
          -- string t, and get a new list of results of type 'b'. Collect
          -- all these list of results, in a 'list of list' ys.
          -- (This is the 'list comprehension syntax' common in Haskell)
          let ys = [runParser (f2 x) t | (x,t) <- xs] in
          concat ys -- concatenate all these lists of results into a single list

-- So can we test our newly created combinator and write a new parser which
-- will accept two digits? Before we do so, let us consider a very simple
-- parser which always succeeds and never processes any of the input string:

inject :: a -> Parser a
inject x = Parser f where
    f s = [(x,s)]  -- Single result: returns x and remainder string same as input

-- It may not be clear at this stage why such a parser is useful. As a first
-- application, imagine we want to write a parser which accepts a digit,
-- but doesn't return the digit itself, and instead returns a string where
-- the digit '0' have been placed in front of the result:

silly1 :: Parser [Char]                 -- same as 'Parser String'
silly1 = combine digit (\x -> inject ['0',x])

-- Can you see what this parser silly1 is doing? It will run the
-- first parser digit, and for each result x will produce the 
-- result ['0',x] without processing the string further.

ex11 :: [(String, String)]              -- same as [([Char], String)]
ex11 = runParser silly1 "34 + 12"       -- [("03","4 + 12")], hurray, '0' in front

-- So maybe we can now write a parser which will accept two consecutive digits
twoDigits1 :: Parser String
twoDigits1 = 
    combine digit $ \d1 ->
        combine digit $ \d2 ->
            inject [d1,d2]
    
-- This parser runs the parser digit on the input string, and uses the resulting
-- digit d1 to run a second parser, which itelf firstly runs the digit parser,
-- and uses the resulting digit d2 to simply inject the string [d1,d2] without
-- further processing. We'd better make sure this works. If it does, then we
-- can see here that despite all odds, the parser 'inject' is pretty useful.

ex12 :: [(String,String)]
ex12 = runParser twoDigits1 "34 + 12"   -- [("34"," + 12")], it works !!

-- It is now time to speak of 'monads'. We have avoided doing so until now
-- to keep things as simple as possible. However, our type constructor
-- 'Parser' (which takes one single argument) has a 'combine' function:
--
-- combine :: Parser a -> (a -> Parser b) -> Parser b
--
-- and it as an 'inject' function
--
-- 'inject' :: a -> Parser a
--
-- This makes 'Parser' a perfect candidate to become a monad. A type 
-- constructor 'm' is said to be a 'Monad' when two key functions are defined:
--
-- return :: a -> m a   -- 'inject' is in fact called 'return' for monads
--
-- (>>=)  :: m a -> (a -> m b) -> m b   -- 'combine' is in fact called 'bind'
--
-- The 'bind' operator (our 'combine') (>>=) is an infix operator which
-- means that instead of writing '(>>=) p1 f2' it is customary to use
-- the infix notation and write 'p1 >>= f2'.

-- So how to we turn our type contructor Parser into a monad ?
-- We simply need to define a monad instance:

instance Monad Parser where
    return = inject
    (>>=)  = combine

-- However, this declaration alone will create an error because Haskell 
-- will not let you define an instance for Monad without first defining
-- an instance for Applicative. If you search for 'Monad' on Hoogle
-- (https://hoogle.haskell.org/) you will find something like:
--
-- 'class Applicative m => Monad m' where ...
--
-- which means that the type class Monad is defined as a subclass of
-- the type class Applicative, or that Applicative is a superclass
-- of Monad. In other words, nothing can be a 'Monad' without being 
-- first an 'Applicative'. In order to define an applicative instance,
-- we need to provide two functions:
--
-- pure :: a -> m a     -- Oh, we already have 'return' (our 'inject')
--
-- (<*>) :: m (a -> b) -> m a -> m b    -- what do we do here ?

-- However, because we intend our Applicative instance to also be a 
-- be a Monad and not just an Applicative, we do not need to do any work
-- and we can simply use the 'ap' function which works for every monad,
-- provided the module 'Control.Monad' is imported.

instance Applicative Parser where
    pure  = return  -- Parser is also a monad, so return will do
    (<*>) = ap      -- defined in Control.Monad for all monads

-- How the function 'ap' is defined is not important at this stage.
-- We really want our 'Parser' type constructor to be a Monad and we
-- can simply use this trick of using the 'ap' function to quickly
-- define an Applicative instance so our Monad instance is accepted
-- by Haskell. However, Haskell will still complain at this stage
--
-- class Functor f => Applicative f where ...
--
-- The problem is that Applicative is a subclass of Functor,
-- and nothing can be an 'Applicative' unless it is first a functor.
-- In order to define an instance of functor for a type constructor
-- 'f', we need to provide the following function:
--
-- fmap :: (a -> b) -> f a -> f b   -- what do we do here ?
-- 
-- Once again there is no need to do any work because our Parser will be
-- a Monad anyway, and there is a function 'liftM' which will do the job:

instance Functor Parser where
    fmap = liftM    -- Don't worry about how liftM is defined

-- So now Haskell is happy and has no more complaints: our type constructor
-- Parser has officially become a Monad. But why do we care?
-- Well for one thing, we can rewrite our twoDigits1 parser in a way
-- which every Haskeller will understand: Haskellers love monads!

-- Using the well-known monadic operators, Haskellers will love this.
twoDigits2 :: Parser String
twoDigits2 = 
    (>>=) digit $ \d1 ->
        (>>=) digit $ \d2 ->
            return [d1,d2]

-- In fact, why not take advantage of the fact that 'bind' is an infix operator:
twoDigits3 :: Parser String
twoDigits3 = 
    digit >>= \d1 ->
        digit >>= \d2 ->
            return [d1,d2]

-- The code is now looking better, but is still somewhat messy and unintuitive.
-- Enter the 'DO NOTATION' !!!

twoDigits4 :: Parser String
twoDigits4 = do 
    d1 <- digit     -- get first digit
    d2 <- digit     -- get second digit
    return [d1,d2]  -- return the result

-- This code is exactly the same from the point of view of Haskell as the previous
-- one. However it is a lot more readable and intuitive, which is the whole point 
-- of using a Monad for parsing: we get code which is a lot simpler and easier to 
-- read, thanks to the 'do notation'.
--
-- But are we sure this still works ?

ex13 :: [(String,String)]
ex13 = runParser twoDigits4 "34 + 12"   -- [("34"," + 12")], yep still works !

-- So we see that working with the type class Monad has allowed us to express
-- a somewhat convoluted parser in very simple terms. There is another
-- class which is probably worth learning at this point, namely the class 
-- Alternative: to define an instance of Alternative we need:
--
-- empty :: m a                 -- a parser which always returns no results []
-- 
-- (<|>) : m a -> m a -> m a    -- a parser which returns results of both parsers 

instance Alternative Parser where
    empty = Parser (const [])
    (<|>) = parseOr             -- remember this combinator ?

-- So now we could define our parser range using (<|>) instead of 'parseOr'
range' :: [Char] -> Parser Char
range' []        = error "range: empty list"
range' [c]       = char c               -- only one possible character in the list
range' (c:cs)    = char c <|> range cs  -- this a little bit nicer, but not much

-- And we could define the digit parser based on our new range parser:
digit' :: Parser Char
digit' = range' "0123456789"

-- And why stop there?
twoDigits5 :: Parser String
twoDigits5 = do 
    d1 <- digit'    -- get first digit
    d2 <- digit'    -- get second digit
    return [d1,d2]  -- return the result

ex14 :: [(String,String)]
ex14 = runParser twoDigits5 "34 + 12"   -- [("34"," + 12")], yep still works !

-- Before we move on, we should say a few words about the failing parser
-- 'empty' which always returns no result. 'empty' is a polymorphic 
-- value of type Parser a. So in particular we can define:

parser2 :: Parser String
parser2 = empty

-- Let us try out this parser on our usual string:
ex15 :: [(String, String)]
ex15 = runParser parser2 "34 + 12"      -- [], no result as expected 

-- This parser is not the same thing as the parser which always succeeds
-- and returns [] without processing the input string.

parser3 :: Parser String
parser3 = return []     -- not the same parser as 'empty'

-- Let us try out this parser on our usual string:
ex16 :: [(String, String)]
ex16 = runParser parser3 "34 + 12"      -- [("","34 + 12")], single result

-- Hence we see that it is important not to confuse the failing parser
-- which returns no results with the successful parser of some type [a]
-- which returns a single result, namely the empty list without processing 
-- the input string.

-- Now that we have a nice Monad to play with, it will be easier to create
-- new parsers. One parser we certainly want to have is the one accepting
-- 'one or more digits'. This parser may be viewed as one which accepts
-- one digit and then accepts 'zero or more digits'. So both parsers
-- 'one or more' and 'zero or more' are certainly very important to us,
-- and can be defined in general for any parser of type 'a'.

plus :: Parser a -> Parser [a]  -- give one or more values of type 'a'
plus p = do
    x  <- p         -- get first value of type a from parser p
    xs <- star p    -- get zero or more values from parser p  
    return (x:xs)   -- return one or more values

star :: Parser a -> Parser [a] -- give zero or more values of type 'a'
star p = return [] <|> plus p  -- return zero value (still a success) *or* 1 & more

-- Note that the two parser combinators plus and star are defined by
-- mutual recursion, since they are calling each other.

-- give one or more digits
ex17 :: [(String, String)]              -- There are two possible results
ex17 = runParser (plus digit) "34 + 12" -- [("3","4 + 12"),("34"," + 12")]

-- give zero or more digits
ex18 :: [(String, String)]              -- There are three possible results
ex18 = runParser (star digit) "34 + 12" 
-- There are now three results: [("","34 + 12"),("3","4 + 12"),("34"," + 12")]

-- It may seem concerning that a parser should give us more than one possible
-- result. Indeed, this indicates an ambiguous parse. However, it may happen
-- that the ambiguities will be lifted as we proceed with the various stages 
-- of parsing. For example, the parser 'star digit' is ambiguous when run 
-- against the string '34 + 12' (it has three successful parse). But what if 
-- we said 'give me zero or more digits, then an empty space, then a '+'. 
-- Would that still be ambiguous? Let us find out:

parser4 :: Parser String
parser4 = do
    cs <- star digit    -- zero or more digits
    _  <- char ' '      -- get a white space
    _  <- char '+'      -- get a '+'
    return $ cs ++ " +" -- just return what has been processed

-- The ambiguity has been lifted, only one successful parse
ex19 :: [(String, String)]
ex19 = runParser parser4 "34 + 12"      -- [("34 +"," 12")], no ambiguity

ex20 :: [(String, String)]
ex20 = runParser parser4 "34 * 12"      -- [], no successful parse at all

-- We are know in a position to parse a full integer
integer1 :: Parser Integer
integer1 = do
    ds <- plus digit    -- get one or more digits
    let n = read ds     -- convert the string into an Integer
    return n            -- just return the integer

-- The parser is ambiguous, but otherwise behaves as normal
ex21 :: [(Integer, String)]             -- parser returns an Integer, not a String
ex21 = runParser integer1 "34 + 12"     -- [(3,"4 + 12"),(34," + 12")], 2 results

-- When defining the parser integer1, all we are doing is using the String parser
-- 'plus digit' and calling the function 'read' on the result of the parse. Hence 
-- we are transforming a String parser into an Integer Parser, using the function 
-- 'read :: String -> Integer'. Since 'Parser' is also an instance of the Functor 
-- type class we can simply write:

integer2 :: Parser Integer
integer2 = fmap read (plus digit)

-- Same result
ex22 :: [(Integer, String)]
ex22 = runParser integer2 "34 + 12"     -- [(3,"4 + 12"),(34," + 12")], 2 results

-- Or indeed, since 'fmap' is also known as the infix operator '(<$>)':
integer :: Parser Integer
integer = read <$> (plus digit)

-- Same result
ex23 :: [(Integer, String)]
ex23 = runParser integer "34 + 12"     -- [(3,"4 + 12"),(34," + 12")], 2 results

-- In fact, we can now write a parser returning an expression, rather than Integer:
eNum :: Parser Expr
eNum = ENum <$> integer

-- Still ambiguous, but we are getting expressions out, not Integers
ex24 :: [(Expr, String)]
ex24 = runParser eNum "34 + 12"         -- [(ENum 3,"4 + 12"),(ENum 34," + 12")]

-- One parser we have not discussed so far is the one accepting white spaces.
-- Of course we have seen (char ' ') but other types of white spaces exists
-- such as '\t' (tab) and '\n' (end of line)

white :: Parser Char 
white = range " \\t\\n"

-- The leading white space has been successfully removed from the input string
ex25 :: [(Char, String)]
ex25 = runParser white " + 12"          -- [(' ',"+ 12")]

-- A possible grammar for the concrete syntax of our language is:
-- Expr -> N                -- Produce an Expr from an integer 
--       | Expr '+' Expr    -- Produce an Expr from two Expr and '+' in between
--       | Expr '*' Expr    -- Produce an Expr from two Expr and '*' in between
--       | '(' Expr ')'     -- Produce an Expr from an Expr surrounded by brackets
-- 
-- Of course, to be precise we would need to spell out the grammar to produce
-- the non-terminal N representing an integer:
--
-- N -> digit               -- Produce an N from a digit
--    | digit N             -- Produce an N from a digit followed by an N
--
-- digit -> '0'             -- Produce a digit from the terminal '0'
--        | '1'             -- Produce a digit from the terminal '1'
--        | '2'             -- Produce a digit from the terminal '2'
--        ...
--
-- Actually we want our concrete syntax to accept white spaces:
-- so we should add a production rule for Expr
--
-- Expr -> Sp Expr          -- Produce an Expr from an Expr preceded by Sp
--       | Expr Sp          -- Produce an Expr from an Expr followed by Sp
--
-- Sp -> ' '
--     | '\t'
--     | '\n' 
--
-- Note that the concrete grammar chosen here allows for ambiguous expressions:
-- 56 * 34 + 12 belongs to the language defined by the grammar yet it is unclear
-- whether this expression of concrete syntax should be parsed as:
-- EAdd (EMul (ENum 56) (ENum 34)) (ENum 12) 
-- or
-- EMul (ENum 56) (EAdd (ENum 34) (ENum 12)) 
--
-- We now want to write a full parser for any expression of our language
-- We shall do so naively by following our grammar to the letter
-- i.e. we are calling a different parser for each production rule
expr1 :: Parser Expr
expr1 =  eNum       -- Expr -> N 
     <|> eAdd1      -- Expr -> Expr '+' Expr
     <|> eMul1      -- Expr -> Expr '*' Expr
     <|> eBracket1  -- Expr -> '(' Expr ')'
     <|> eLeft1     -- Expr -> Sp Expr
     <|> eRight1    -- Expr -> Expr Sp

eAdd1 :: Parser Expr
eAdd1 = do
    e  <- expr1         -- get a first expression
    _  <- char '+'      -- expect the char '+' at this stage
    e' <- expr1         -- get a second expression
    return $ EAdd e e'

eMul1 :: Parser Expr
eMul1 = do
    e  <- expr1         -- get a first expression
    _  <- char '*'      -- expect the char '*' at this stage
    e' <- expr1         -- get a second expression
    return $ EMul e e'

eBracket1 :: Parser Expr
eBracket1 = do
    _ <- char '('       -- expects '('
    e <- expr1          -- get an expression 
    _ <- char ')'       -- expects '}'
    return e

eLeft1 :: Parser Expr
eLeft1 = do
    _ <- white          -- get a white space
    e <- expr1          -- get an expression
    return e

eRight1 :: Parser Expr
eRight1 = do
    e <- expr1          -- get an expression
    _ <- white          -- get a white space
    return e

-- DO NOT TRY TO EVALUATE ex26 on ghci, your computer will be in an infinite loop
ex26 :: [(Expr, String)]
ex26 = runParser expr1 "34 + 12"

-- unfortunately, naively following the structure of the grammar leads to failure,
-- whereby the parser gets into an infinite search loop. The parser aggregates
-- the results of 6 different parsers corresponding to each production rule of
-- the grammar. The parser failing to terminate must be due to the fact that one
-- of these six parsers fails to terminate.

-- This terminates with two successful parse but does not consume whole string.
ex26_1 :: [(Expr, String)]
ex26_1 = runParser eNum "34 + 12"

-- This also terminates and with no successful parse as expected
ex26_2 :: [(Expr, String)]
ex26_2 = runParser eBracket1 "34 + 12"

-- This also terminates and with no successful parse as expected
ex26_3 :: [(Expr, String)]
ex26_3 = runParser eLeft1 "34 + 12"

-- This does not terminate. What is the problem? It is looking for an expression
-- followed by a white space. But when looking for an expression, part of the
-- work will be to look for an expression followed by a white space. We can 
-- see there is an inifinite loop.
ex26_4 :: [(Expr, String)]
ex26_4 = runParser eRight1 "34 + 12"

-- This does not terminate. What is the problem? It is looking for an expression
-- followed by the terminal symbol '+' followed by an expression. But when 
-- looking for the first expression, part of the work will be to look for an
-- expression followed by '+' followed by an expression. 
ex26_5 :: [(Expr, String)]
ex26_5 = runParser eMul1 "34 + 12"

-- This does not terminate
ex26_6 :: [(Expr, String)]
ex26_6 = runParser eAdd1 "34 + 12"

-- The problem is our grammar has left recursion. We need to transform it
-- into an equivalent grammar where left recursion has been removed.
-- Following the paper: "Removing Left Recursion from Context-Free Grammars"
-- Robert C. Moore, Microsoft Research

-- Our grammar is of the form:
--
-- Non left-recursive rules
-- E -> N 
--    | Sp E 
--    | '(' E ')'
--
-- Left-recursive rules
-- E -> E e1    -- e1 = '+' E
--    | E e2    -- e2 = '*' E
--    | E e3    -- e3 = Sp

-- Following the paper, a non left-recursive yet equivalent grammar is
--
-- E -> N
--    | N E'
--    | Sp E
--    | Sp E E'
--    | '(' E ')'
--    | '(' E ')' E'
--
--  where the production rules for E' are as follows:
-- 
-- E' -> e1
--     | e1 E'
--     | e2 
--     | e2 E'
--     | e3
--     | e3 E'


-- Let us define a custom type for the data returned by an E' parser
data E'
    = AddE   Expr       -- parser finds a '+' then an expression
    | AddEE' Expr E'    -- parser finds a '+' then an expression then an E'
    | MulE   Expr       -- parser finds a '*' then an expression
    | MulEE' Expr E'    -- parser finds a '*' then an expression then an E'
    | Sp                -- parser finds a white space, nothing to return 
    | SpE'   E'         -- parser finds a white space then an E' 

-- We assume we have already written a parser expr :: Parser Expr and we wish
-- to write a parser which corresponds to the non-terminal E'. Recall the
-- production rules:
-- E' -> + E
--     | + E E'
--     | * E 
--     | * E E'
--     | Sp
--     | Sp E'

expr' :: Parser E'
expr' = pAddE <|> pAddEE' <|> pMulE <|> pMulEE' <|> pSp <|> pSpE'
    where
        pAddE = do
            _ <- char '+'               -- expects a '+'
            e <- expr                   -- expects an expression
            return $ AddE e

        pAddEE' = do
            _  <- char '+'              -- expects a '+'
            e  <- expr                  -- expects an expression
            e' <- expr'                 -- expects an E'
            return $ AddEE' e e'

        pMulE   = do
            _ <- char '*'               -- expects a '*'
            e <- expr                   -- expects an expression
            return $ MulE e

        pMulEE' = do
            _  <- char '*'              -- expects a '*'
            e  <- expr                  -- expects an expression
            e' <- expr'                 -- expects an E'
            return $ MulEE' e e'

        pSp     = do
            _ <- white                  -- expects a whitespace
            return Sp

        pSpE'   = do
            _  <- white                 -- expects a whitespace
            e' <- expr'                 -- expects an E'
            return $ SpE' e'

-- main parser, parsing for E. Recall the production rules:
-- E -> N
--    | N E'
--    | Sp E
--    | Sp E E'
--    | '(' E ')'
--    | '(' E ')' E'

expr :: Parser Expr
expr = pNum <|> pNumE' <|> pSpE <|> pSpEE' <|> pBrEBr <|> pBrEBrE'

-- Parser which combines and Expr with an E' without processing string
-- This parser may return more than one successful parse
-- THIS IS UNEXPLAINED AND HARD TO UNDERSTAND
glue :: Expr -> E' -> Parser Expr
glue e e' = Parser f where
    f s = case e' of
      AddE e2       -> [(EAdd e e2,s)]  -- one parse, same string 
      AddEE' e2 e2' -> runParser (glue (EAdd e e2) e2') s
                    ++ (map (\(e3,s') -> (EAdd e e3, s')) $ runParser (glue e2 e2') s)
      MulE e2       -> [(EMul e e2,s)]  -- one parse, same string 
      MulEE' e2 e2' -> runParser (glue (EMul e e2) e2') s
                    ++ (map (\(e3,s') -> (EMul e e3, s')) $ runParser (glue e2 e2') s)
      Sp            -> [(e,s)]          -- one parse, same string
      SpE' e2'      -> runParser (glue e e2') s

pNum :: Parser Expr
pNum = eNum

pNumE' :: Parser Expr
pNumE' = do
    n  <- eNum
    e' <- expr'
    glue n e'

pSpE :: Parser Expr
pSpE = do
    _ <- white
    expr

pSpEE' :: Parser Expr
pSpEE' = do
    _  <- white
    e  <- expr
    e' <- expr'
    glue e e' 

pBrEBr :: Parser Expr
pBrEBr = do
    _ <- char '('
    e <- expr
    _ <- char ')'
    return e

pBrEBrE' :: Parser Expr
pBrEBrE' = do
    _  <- char '('
    e  <- expr
    _  <- char ')'
    e' <- expr'
    glue e e'

-- So far so good
ex27 :: [(Expr, String)]
ex27 = runParser expr "34"              -- [(ENum 3,"4"),(ENum 34,"")] 

-- Now we'd like to see only the results which process the whole string
parse' :: String -> [Expr]
parse' = map fst . filter (null . snd) . runParser expr 

-- nice, only one result
ex28 :: [Expr]
ex28 = parse' "34"                      -- [ENum 34]

-- many duplicated results
ex29 :: [Expr]
ex29 = parse' "    34   "               -- [ENum 34,ENum 34,ENum 34,....]

-- let us remove duplicated results
parse :: String -> [Expr]
parse = nub . map fst . filter (null . snd) . runParser expr 

-- nice, only one result
ex30 :: [Expr]
ex30 = parse "    34   "                -- [ENum 34]

-- no result as expected
ex31 :: [Expr]
ex31 = parse "  3 4  "                  -- []

-- beautiful
ex32 :: [Expr]
ex32 = parse "34 + 12"                  -- [EAdd (ENum 34) (ENum 12)]

-- can cope with extra spaces and brackets....
ex33 :: [Expr]
ex33 = parse "   ((34)    + 12)  "      -- [EAdd (ENum 34) (ENum 12)]

-- very nice, one single result
ex34 :: [Expr]
ex34 = parse "56 * (34 + 12)"           -- [EMul (ENum 56) (EAdd (ENum 34) (ENum 12))]

--[EMul (ENum 56) (EAdd (ENum 34) (ENum 12)),EAdd (EMul (ENum 56) (ENum 34)) (ENum 12)]
-- The parser correctly sees that there are two possible interpretations
-- 56 * (34 + 12) ans (56 * 34) + 12
ex35 :: [Expr]
ex35 = parse "56 * 34 + 12"           

