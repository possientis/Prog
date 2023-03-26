-- Proxy Design Pattern
--
-- This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
-- https://www.youtube.com/watch?v=XvbDqLrnkmA

-- A proxy is a class which functions as an interface to something else

-- There are three participants to the proxy design pattern:
--
-- 1. subject
-- 2. real subject
-- 3. proxy
--

-- The subject is the common interface between the real object and proxy
-- the real object is that which the proxy is meant to be substituted for

-- This is the subject
class ComponentPrice a where
  getCpuPrice :: a -> IO Double
  getRamPrice :: a -> IO Double
  getSsdPrice :: a -> IO Double

-- This is the real subject
data StoredComponentPrice = StoredComponentPrice
instance ComponentPrice StoredComponentPrice where
  getCpuPrice StoredComponentPrice = return 250.0
  getRamPrice StoredComponentPrice = return 32.0
  getSsdPrice StoredComponentPrice = return 225.0

-- This is the proxy
data ProxyComponentPrice = ProxyComponentPrice
instance ComponentPrice ProxyComponentPrice where
  getCpuPrice ProxyComponentPrice = getRequestFromServer CPU
  getRamPrice ProxyComponentPrice = getRequestFromServer RAM
  getSsdPrice ProxyComponentPrice = getRequestFromServer SSD

data Request = CPU | RAM | SSD deriving Show

getRequestFromServer :: Request -> IO Double 
getRequestFromServer = sendRequest serverInstance

data Server = Server
serverInstance :: Server
serverInstance = Server
startServer :: IO ()
startServer = do
  putStrLn "Component price server running, awaiting request"
  return ()


sendRequest :: Server -> Request -> IO Double
sendRequest Server request = do
  putStrLn ("Server receiving request for " ++ (show request) ++ " price")
  -- In our example, server code uses real subject
  let component = StoredComponentPrice  -- real subject
  putStrLn ("Server responding to request for " ++ (show request) ++ " price")
  case request of
    CPU       -> getCpuPrice component
    RAM       -> getRamPrice component
    SSD       -> getSsdPrice component
    
main :: IO ()
main = do
  startServer
  -- we can use proxy as if it was real, making client code a lot easier
  let prices  = ProxyComponentPrice
  cpu <- getCpuPrice prices 
  ram <- getRamPrice prices
  ssd <- getSsdPrice prices
  putStrLn ("The CPU price is " ++ (show cpu))
  putStrLn ("The RAM price is " ++ (show ram))
  putStrLn ("The SSD price is " ++ (show ssd))
  return ()





