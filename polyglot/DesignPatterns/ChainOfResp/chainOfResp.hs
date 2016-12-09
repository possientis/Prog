-- Chain of Responsibility Design Pattern
import Data.List(intercalate)
-- The Chain Of Responsibility design pattern is meant to decouple
-- clients (which may have various requests) from request handlers
-- which may be of different types. Rather than forcing a client
-- to have the precise knowledge of which request handler is able
-- to deal with which type of request, the Chain of Responsibility
-- design pattern creates a common base interface to all request
-- handlers, and unites them into a single linked list (a 'chain').
-- Now the client only needs to know the head of the chain, to
-- which it sends all of its requests. Each request handler, apart
-- from maintaining a link to a 'successor', fundamentally has
-- a 'handleRequest' method which now accepts all types of request.
-- However, when faced with a request which it cannot fulfill, a 
-- request handler will pass on the request to its successor. 
-- Provided the chain of request handlers is properly set up, all
-- requests should be handled appropriately.
--
-- Note that this pattern can be generalized from 'chains' to non
-- linear structure between objects, such as trees. One can imagine
-- a network of request handlers, which are either dealing with 
-- request themselves, or passing requests to other (linked) 
-- request handlers
--
-- This coding exercise is meant to provide a simulation of an ATM
-- machine. As a server, the machine is able to provide a service
-- 'getAmount' to an external client which consists in the delivery
-- of the appropriate set of bank notes which corresponds to a 
-- desired amount. As a client, the ATM machine relies on various
-- request handlers, namely those which are specialized in the delivery
-- of specific bank notes. So the machine relies on a service for the 
-- delivery of $5 notes, another service for the delivery of $10 notes
-- and so forth. This is a case where the Chain of Responsibility 
-- design pattern can be successfully applied, allowing the implementation 
-- of the ATM machine to forget about all those different services and 
-- the details of how to convert an amount of cash into a set of notes.
--
--
-- Our ATM machine only need to worry about the head of the chain of
-- services, which it maintains as an internal data member. This machine
-- has the ability to provide a set of bank notes from a desired amount
data ATMMachine = ATMMachine { machineHandler :: RequestHandler }

newATMMachine :: ATMMachine
newATMMachine  = ATMMachine getHandlingChain

getHandlingChain :: RequestHandler
getHandlingChain =  RequestHandlerForFifty  $
                    RequestHandlerForTwenty $ 
                    RequestHandlerForTen    $
                    RequestHandlerForFive  RequestHandlerNull

getAmount :: ATMMachine -> Int -> [BankNote]
getAmount machine amount = handleRequest (machineHandler machine) amount 

getAmountWithIO :: ATMMachine -> Int -> IO [BankNote]
getAmountWithIO machine amount = do
  putStrLn ("ATM Machine: requesting amount of $" ++ (show amount))
  return $ getAmount machine amount

-- This is the main typeuniting all request handlers into a common interface.
data RequestHandler = RequestHandlerForFifty  { next :: RequestHandler }
                    | RequestHandlerForTwenty { next :: RequestHandler }
                    | RequestHandlerForTen    { next :: RequestHandler }
                    | RequestHandlerForFive   { next :: RequestHandler }
                    | RequestHandlerNull deriving Eq


handleRequest :: RequestHandler -> Int -> [BankNote]
handleRequest handler amount
  | amount  < 0       = error "Illegal argument" 
  | amount == 0       = []    -- empty list  
  | mod amount 5 /= 0 = error "Requested amount should be multiple of $5"
  | amount >= value   = denom:(handleRequest handler (amount - value))
  | successor /= null = handleRequest successor amount   
  | otherwise         = error "Illegal state exception" -- chain badly set up
  where denom         = denomination handler
        value         = noteValue denom 
        successor     = next handler
        null          = RequestHandlerNull


denomination :: RequestHandler -> BankNote
denomination   (RequestHandlerForFifty  _ ) = Fifty
denomination   (RequestHandlerForTwenty _ ) = Twenty
denomination   (RequestHandlerForTen    _ ) = Ten
denomination   (RequestHandlerForFive   _ ) = Five
denomination    RequestHandlerNull          = error "Null pointer exception"


data BankNote = Five | Ten | Twenty | Fifty
noteValue :: BankNote -> Int
noteValue    Five      = 5
noteValue    Ten       = 10
noteValue    Twenty    = 20
noteValue    Fifty     = 50

instance Show BankNote where
  show note = show $ noteValue note

main :: IO ()
main = do
  let atm   = newATMMachine
  list  <- getAmountWithIO atm 235
  let str = "[" ++ intercalate ", " (map show (reverse list)) ++ "]" 
  putStrLn "The notes handed out by the ATM machine are:"
  putStrLn str




