import Control.Monad        (ap, liftM)
import Control.Applicative  (Alternative (..))

-- Let us consider the following abstract syntax for a very simple language
data Expr
    = ENum Integer
    | EAdd Expr Expr
    | EMul Expr Expr
    deriving (Show)     -- Show instance so haskell can print expressions

-- Example of expressions are as follows:

-- 34                                           -- concrete syntax
e0 :: Expr
e0 = ENum 34                                    -- abstract syntax

-- 34 + 12                                      -- concrete syntax
e1 :: Expr
e1 = EAdd (ENum 34) (ENum 12)                   -- abstract syntax

-- 34 * 12                                      -- concrete syntax
e2 :: Expr
e2 = EMul (ENum 34) (ENum 12)                   -- abstract syntax

-- 56 * (34 + 12)                               -- concrete syntax
e3 :: Expr
e3 = EMul (ENum 56) (EAdd (ENum 34) (ENum 12))  -- abstract syntax

-- The notion of abstract syntax is very important as all the programming is done
-- around it. It would be very difficult and messy to deal with the concrete 
-- syntax directly. For example, the abstract syntax allows to write an interpreter:

eval :: Expr -> Integer
eval (ENum n) = n
eval (EAdd e e') = eval e + eval e'
eval (EMul e e') = eval e * eval e'

-- But of course, a real program needs to read the concrete syntax provided by
-- the user, either directly from the terminal, or from a source file. In fact
-- this very file is written using Haskell's concrete syntax.

-- Enters the notion of parsing: it is the process of converting the concrete
-- syntax into the abstract syntax, a very important process.

-- On the face of it, parsing appears to be the design of a function:
parse1 :: String -> Expr
parse1 = undefined  -- parse1 "34 + 12" should be e1

-- While this conception of parsing is correct, it is not a good way to approach 
-- the problem, because parsing is the result of processing a string bits by bits,
-- and we want to be able to represent all the intermediate stages of parsing.
-- Hence a better approach would be to aim at writing a function:

parse2 :: String -> (Expr, String)
parse2 = undefined  -- parse2 "34 + 12" should be (ENum 34, "+ 12")

-- This function would return an expression, together with the remainder of the
-- input String which was not processed and remains to be analysed.

-- Note that there is no fundamental difference between (Expr, String) and 
-- (String, Expr). Our choice of order is arbitrary and we could equally have:

parse3 :: String -> (String, Expr)
parse3 = undefined  -- parse3 "34 + 12" should be ("+ 12", ENum 34)

-- However, this does not work either: it is very unlikely that all intermediate
-- stages of parsing will lead to a valid expression of the abstract syntax.
-- In fact, from the string "34 + 12" we could extract the expression "ENum 34",
-- but we are then left with the string "+ 12" from which we would like to consume
-- or process the '+'. So parse2 "+ 12" should be (???,"12") but we do not have an 
-- expression of the abstract syntax to return.

-- As we do not want to return a meaningful expression, we need a parser:
parse4 :: String -> ((),String)
parse4 = undefined

-- Sometimes we may want our parser to return a simple character, so we need:
parse5 :: String -> (Char, String)
parse5 = undefined

-- or we may want to get an integer:
parse6 :: String -> (Integer, String)
parse6 = undefined

-- So it appears we need different types of parsers depending on what it is we 
-- expect at a given intermediary stage of our parsing.

-- Dealing with all these different types is cumbersome. Luckily, Haskell has
-- polymorphism which allows us to express all these different types as one.

parse7 :: String -> (a, String)
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

-- The polymorphic type String -> [(a, String)] seems to be the right type
-- to consider, and we should give it a name. One solution is a type synonym:

type Parser1 a = String -> [(a, String)]

-- So now we do not need to write String -> [(a, String)] everywhere and we
-- can simply write 'Parser1 a' which is not only shorter, but also more
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

-- The type 'Parser3 a' has only one data constructor, unlike our abstract
-- syntax Expr which has three. While it is perfectly possible to use the 'data'
-- keyword to define a new type with a single constructor, most people prefer
-- using the 'newtype' keyword:

newtype Parser4 a = Parser4 (String -> [(a, String)])

-- Unlike type synonyms which are regarded as the same type by Haskell, declaring
-- a newtype will ensure it cannot be mixed up with (String -> [(a, String)]).
-- Unlike types declared with 'data', a newtype will be as efficient at runtime
-- as the underlying type String -> [(a, String)].

-- It is very common when declaring a newtype to use the syntax:

newtype Parser a = Parser { runParser :: String -> [(a, String)] }

-- This syntax allows you to declare both the type and an accessor for the newtype
-- runParser :: Parser a -> String -> [(a, String)]. 
-- which is a function which extracts the underlying function from the parser.

-- So if we had a parser for exression:
parser1 :: Parser Expr
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
-- possible result which is unambiguous.
--
-- A parse which yields the empty string "" is also good: there is no more input
-- to process and the parse was in fact successful.

-- Another advantage of declaring our type 'Parser a' is that it allows us to
-- free our brain from remembering the details of what a parser really is. A
-- value of type 'Parser a' (aka a parser of type 'a') is something which you can
-- run against a string using 'runParser' to obtain a value of type 'a' together 
-- with the remainder of the input string which needs to be processed.

-- Now that we have settled our Parser type, we need to start writing parsers.

-- One parser which is bound to be useful is a 'Char' parser which returns
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
-- with the parser p2, to obtain more results. This is about combining parsers:

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
-- second parser should be of type 'Parser [Char]'. However, it should 
-- also return the digit which was found from running the first parser.
-- So the result of our second parser should depend on the outcome of the
-- first parser. In other words, we cannot have the same second parser 
-- across the board, we need to make the second parser depend on the result
-- of the first. So let us try the following signature instead:

combine :: Parser a -> (a -> Parser b) -> Parser b

-- We are hoping this signature will do. It allows us to have a different 
-- second parser, depending on the result of type 'a' obtained from the
-- first parser. So let us try and implement this parser combinator:

combine p1 f2 = Parser f where
          -- get all results from running the first parser p1 on input string s
    f s = let xs = runParser p1 s in 
          -- For each result (x,t), run the parser (f2 x) on the remainder
          -- string t, and get a new list of results of type 'b'. Collect
          -- all these list of results, in a 'list of list' ys.
          -- This is the 'list comprehension syntax' common in Haskell
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

-- Can you see what this parser silly1 is doing. It will run the
-- first parser digit, and for each result 'x' will produce the 
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

-- It is now time to speak of monads. We have avoided doing so until now
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
-- will not let you define an instance 'Monad' without first defining
-- an instance for 'Applicative'. If you search for 'Monad' on Hoogle
-- (https://hoogle.haskell.org/) you will find something like:
--
-- 'class Applicative m => Monad m' where ...
--
-- which means that the type class 'Monad' is defined as a subclass of
-- the type class 'Applicative', or that 'Applicative' is a superclass
-- of 'Monad'. In other words, nothing can be a monad without being 
-- first an applicative. In order to define an applicative instance,
-- we need to provide two functions:
--
-- pure :: a -> m a     -- Oh we already have 'return' (our 'inject')
--
-- (<*>) :: m (a -> b) -> m a -> m b

-- However, because we intend that our applicative instance will also
-- be a monad and not just an applicative, we do not need to do any work
-- and we can simply use the 'ap' function which works for every monad,
-- provided the module 'Control.Monad' is imported.

instance Applicative Parser where
    pure  = return  -- Parser is also a monad, so return will do
    (<*>) = ap      -- defined in Control.Monad for all monads

-- How the function 'ap' is defined is not very important at this stage.
-- We really want our 'Parser' type constructor to be a Monad and we
-- can simply use this trick of using the 'ap' function to quickly
-- define an Applicative instance so our Monad instance is accepted
-- by Haskell. However, Haskell will still complain at this stage
--
-- class Functor f => Applicative f where ...
--
-- The problem is that 'Applicative' is a subclass of 'Functor',
-- and nothing can be an applicative unless it is first a functor.
-- In order to define an instance of functor for a type constructor
-- 'f', we need to provide the following function:
--
-- fmap :: (a -> b) -> f a -> f b
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

-- In fact, why not take advantage of the fact that bind is an infix operator:
twoDigits3 :: Parser String
twoDigits3 = 
    digit >>= \d1 ->
        digit >>= \d2 ->
            return [d1,d2]

-- The code is now looking better, but this is still somewhat messy and
-- unintuitive: enter the 'DO NOTATION' !!!

twoDigits4 :: Parser String
twoDigits4 = do 
    d1 <- digit     -- get first digit
    d2 <- digit     -- get second digit
    return [d1,d2]  -- return the result

-- This means exactly the same thing has before to Haskell, but is a lot
-- more readable and intuitive. This is the whole point of using a Monad
-- for parsing: we get code which is a lot simpler and easier to read.
-- Very nice ! But are we sure this still works ?

ex13 :: [(String,String)]
ex13 = runParser twoDigits4 "34 + 12"   -- [("34"," + 12")], yep still works !

-- So we see that working with the type class Monad has allowed us to express
-- a somewhat convoluted parser in very simple terms. There is another
-- class which is probably worth learning about here, namely the 
-- class 'Alternative'. To define an instance of Alternative we need:
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
range' (c:cs)    = char c <|> range cs  -- this a little bit nicer, not much

-- And we could define the digit parser based on our new range parser:
digit' :: Parser Char
digit' = range' "0123456789"

-- And why stop there?
twoDigits5 :: Parser String
twoDigits5 = do 
    d1 <- digit'     -- get first digit
    d2 <- digit'     -- get second digit
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

-- This parser is not the same things as the parser which always succeeds
-- and returns [] without processing the input string.

parser3 :: Parser String
parser3 = return []     -- not the same parser as 'empty'

-- Let us try out this parser on our usual string:
ex16 :: [(String, String)]
ex16 = runParser parser3 "34 + 12"      -- [("","34 + 12")], single result

-- Hence we see that it is important not to confuse the failing parser
-- which returns no results with the successful parser which returns
-- a single result, namely the empty list without processing the input string.

-- Now that we have a nice Monad to play with, it will be easier to create
-- new parsers. One parser we certainly want to have is the one accepting
-- 'one or more digits'. This parser may be viewed as one which accepts
-- one digit and then accepts 'zero or more digits'. So both parsers
-- 'one or more' and 'zero or more' are certainly very important to us,
-- and can be defined in general for any parser of type 'a'.

plus :: Parser a -> Parser [a]  -- give one or more values of type 'a'
plus p = do
    x  <- p         -- get first value of type a
    xs <- star p    -- get zero or more values   
    return (x:xs)   -- return one or more values

star :: Parser a -> Parser [a] -- give zero or more values of type 'a'
star p = return [] <|> plus p  -- return zero value (still a success) or 1 & more

-- give one or more digits
ex17 :: [(String, String)]              -- There are two possible results
ex17 = runParser (plus digit) "34 + 12" -- [("3","4 + 12"),("34"," + 12")]


-- give zero or more digits
ex18 :: [(String, String)]              -- There are three possible results
ex18 = runParser (star digit) "34 + 12" 
-- There are now three results: [("","34 + 12"),("3","4 + 12"),("34"," + 12")]

-- It may seem concerning that a parser should give us more than one possible
-- result. Indeed, this indicates an ambiguous parse. However, it may happen
-- that the ambiguities will be lifted as we proceed with the various
-- stages of parsing. For example, the parser 'star digit' is ambiguous when
-- run against the string '34 + 12'. But what if we said 'give me zero or
-- more digits, then an empty space, then a '+'. Would that still be
-- ambiguous? Let us find out:

parser4 :: Parser String
parser4 = do
    cs <- star digit    -- zero or more digits
    _  <- char ' '      -- get a white space
    _  <- char '+'      -- get a '+'
    return $ cs ++ " +" -- just return what has been processed

-- The ambiguity has been lifted
ex19 :: [(String, String)]
ex19 = runParser parser4 "34 + 12"      -- [("34 +"," 12")], no ambiguity

ex20 :: [(String, String)]
ex20 = runParser parser4 "34 * 12"      -- [], no successful parse at all

-- We are know in a position to parse a full integer
integer1 :: Parser Integer
integer1 = do
    ds <- plus digit    -- get one or more digits
    let n = read ds     -- convert the string into an Integer
    return n

-- The parser is ambiguous, but otherwise behaves as normal
ex21 :: [(Integer, String)]
ex21 = runParser integer1 "34 + 12"     -- [(3,"4 + 12"),(34," + 12")], 2 results

-- When defining the parser integer1, all we are doing is using the parser
-- (plus digit) :: Parser String and calling the function 'read' on the result 
-- of the parse. Hence we are transforming a 'Parser String' into a 
-- 'Parser Integer', using the function 'read :: String -> Integer'.
-- Since 'Parser' is also an instance of the 'Functor' type class we can
-- simply write:

integer2 :: Parser Integer
integer2 = fmap read (plus digit)

-- Same result
ex22 :: [(Integer, String)]
ex22 = runParser integer2 "34 + 12"     -- [(3,"4 + 12"),(34," + 12")], 2 results

-- Or indeed, since 'fmap' is also known as the infix operator '(<$>)':
integer :: Parser Integer
integer = read  <$> (plus digit)

-- Same result
ex23 :: [(Integer, String)]
ex23 = runParser integer "34 + 12"     -- [(3,"4 + 12"),(34," + 12")], 2 results

-- In fact, we can now write a parser returning an expression:
eNum :: Parser Expr
eNum = ENum <$> integer

-- Still ambiguous, but we are getting expressions out
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

-- We now want to write a full parser for any expression of our language
-- THE FOLLOWING IS VERY NAIVE AND DOES NOT WORK. The parser keeps calling
-- itself and never terminates. But it is still interesting to look at.
expr1 :: Parser Expr
expr1 = do
    _ <- star white     -- remove leading white spaces
    -- get an ENum, EAdd or EMul type expression, or a bracketted expression
    e <- eNum <|> eAdd1 <|> eMul1 <|> eBracket1
    _ <- star white     -- remove trailing white spaces
    return e

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

-- Don't try this at home, your computer will be in an infinite loop
ex26 :: [(Expr, String)]
ex26 = runParser expr1 "34 + 12"


-- STILL IN TRYING STAGES
-- Following the paper: "Removing Left Recursion from Context-Free Grammars"
-- Robert C. Moore

expr :: Parser Expr
expr = eNum <|> eNumExpr' <|> eBracket

eBracket :: Parser Expr
eBracket = do
    _ <- char '('       -- expects '('
    e <- expr          -- get an expression 
    _ <- char ')'       -- expects '}'
    return e

eNumExpr' :: Parser Expr
eNumExpr' = do
    n     <- eNum
    (c,e) <- expr'
    if c == '+'
        then return $ EAdd n e
        else return $ EMul n e

expr' :: Parser (Char, Expr)
expr' = do
    c <- op
    e <- expr <|> 
        do
            e <- expr
            (c',e') <- expr'
            if c' == '+'
                then return $ EAdd e e'
                else return $ EMul e e'
    return (c,e)

ex27 :: [(Expr, String)]
ex27 = runParser expr "56*34+12"

parse :: String -> Either String Expr
parse s = case map fst $ filter (null . snd) $ runParser expr s of
    []  -> Left "Cannot parse input string"
    [e] -> Right e
    xs  -> Left $ "Ambiguous parse: " ++ show xs

ex28 :: Either String Expr
ex28 = parse "56*(23+12)"       -- Right (EMul (ENum 56) (EAdd (ENum 23) (ENum 12)))

ex29 :: Either String Expr
ex29 = parse "some gibberish"   -- Left "Cannot parse input string"

ex30 :: Either String Expr
ex30 = parse "(34+12)*56"
