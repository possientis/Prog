module Main

import Data.Vect 

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString   = String
SchemaType SInt      = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

{- Using record syntax gives accessors for free
data DataStore : Type where
  MkData : (schema : Schema) 
        -> (size : Nat) 
        -> (items : Vect size (SchemaType schema)) 
        -> DataStore

total 
schema : DataStore -> Schema
schema (MkData schema' _ _) = schema'

total
size : DataStore -> Nat
size (MkData _ size' _) = size'


total
items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
items (MkData _ _ items') = items'
-}

record DataStore where
  constructor MkData
  schema : Schema
  size   : Nat
  items  : Vect size (SchemaType schema)

total
addToStore : (store: DataStore) 
          -> (SchemaType (schema store)) 
          -> DataStore

addToStore (MkData schema size items) newItem = 
  MkData schema _ (addToData items) where
    addToData : Vect old     (SchemaType schema) 
             -> Vect (S old) (SchemaType schema)
    addToData []        = [newItem]
    addToData (x :: xs) = x :: addToData xs

display : SchemaType schema -> String
display {schema = SString} item    = item
display {schema = SInt} item        = show item
display {schema = (x .+. y)} (a, b) = display a ++ ", " ++ display b


total
getEntry : (pos : Integer) 
        -> (store : DataStore) 
        -> Maybe (String, DataStore)
getEntry pos store = 
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing  => Just ("Out of range\n", store)
           Just id  => 
              let entry = index id store_items in
                  Just (display entry, store)

data Command : Schema -> Type where
  Add  : SchemaType a -> Command a
  Get  : Integer      -> Command a
  Size :                 Command a
  Quit :                 Command a  

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString   input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) =
      case span (/= '"') xs of
           (quoted, '"' :: rest)  => Just (pack quoted, ltrim (pack rest))
           _                      => Nothing
    getQuoted _                   =  Nothing

parsePrefix SInt      input = 
  case span isDigit input of
       ("" , rest) => Nothing
       (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) input =
  case parsePrefix schemal input of
       Nothing              => Nothing
       Just (l_val, input') =>
        case parsePrefix schemar input of
             Nothing  => Nothing
             Just (r_val, input'') => Just ((l_val, r_val), input'')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = 
  case parsePrefix schema input of
       Just (res, "") => Just res
       Just _         => Nothing
       Nothing        => Nothing

total
parseCommand : (schema : Schema) 
            -> (cmd : String) 
            -> (args : String) 
            -> Maybe (Command schema)
parseCommand schema "add" str = 
  case parseBySchema schema str of
       Nothing  => Nothing
       Just dat => Just (Add dat)
parseCommand _ "get" val =
  let val' = trim val in
      if (all isDigit (unpack val')) && val' /= ""
        then Just (Get (cast val'))
        else Nothing
parseCommand _ "size" "" = Just Size
parseCommand _ "quit" "" = Just Quit
parseCommand _ _      _  = Nothing


total
parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = 
  case span (/= ' ') input of
       (cmd,args) => parseCommand schema cmd (ltrim args)

total
processCommand : (store : DataStore) 
              -> (cmd : Command (schema store)) 
              -> Maybe (String, DataStore)
processCommand _      Quit       = Nothing
processCommand store  Size       =
  Just ("size: " ++ show (size store) ++ "\n", store)
processCommand store  (Add x)    = 
  Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
processCommand store  (Get pos)  = getEntry pos store

total
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp =
  case parse (schema store) inp of
       Nothing    => Just ("Invalid command\n", store)
       (Just cmd) => processCommand store cmd

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "Command: " processInput

