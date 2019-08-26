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

{-
data Command 
  = Add String
  | Get Integer
  | Size
  | Quit



total
addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newItem = MkData _ (addToData items) where
  addToData : Vect old String -> Vect (S old) String
  addToData [] = [newItem]
  addToData (x :: xs) = x :: addToData xs

total
parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add (trim str))
parseCommand "get" val =
  let val' = trim val in
      if (all isDigit (unpack val')) && val' /= ""
        then Just (Get (cast val'))
        else Nothing
parseCommand "size" "" = Just Size
parseCommand "quit" "" = Just Quit
parseCommand _      _  = Nothing

total
parse : (input : String) -> Maybe Command
parse input = 
  case span (/= ' ') input of
       (cmd,args) => parseCommand cmd args

total
getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = 
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing  => Just ("Out of range\n", store)
           Just id  => 
              let entry = index id store_items in
                  Just (entry ++ "\n", store)

total
processCommand : (cmd : Command) 
              -> (store : DataStore) 
              -> Maybe (String, DataStore)
processCommand Quit _        = Nothing
processCommand Size store    =
  Just ("size: " ++ show (size store) ++ "\n", store)
processCommand (Add x) store = 
  Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
processCommand (Get pos) store = getEntry pos store

total
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp =
  case parse inp of
       Nothing    => Just ("Invalid command\n", store)
       (Just cmd) => processCommand cmd store

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
-}
