module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

data Command 
  = Add String
  | Get Integer
  | Quit

total
parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add (trim str))
parseCommand "get" val =
  let val' = trim val in
      if (all isDigit (unpack val')) && val' /= ""
        then Just (Get (cast val'))
        else Nothing
parseCommand "quit" "" = Just Quit
parseCommand _      _  = Nothing

parse : (input : String) -> Maybe Command
parse input = 
  case span (/= ' ') input of
       (cmd,args) => parseCommand cmd args

size : DataStore -> Nat
size (MkData size items) = size

items : (store : DataStore) -> Vect (size store) String
items (MkData size items) = items

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newItem = MkData _ (addToData items) where
  addToData : Vect old String -> Vect (S old) String
  addToData [] = [newItem]
  addToData (x :: xs) = x :: addToData xs

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = 
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing  => Just ("Out of range\n", store)
           Just id  => 
              let entry = index id store_items in
                  Just (entry ++ "\n", store)

processCommand : (cmd : Command) 
              -> (store : DataStore) 
              -> Maybe (String, DataStore)
processCommand Quit _        = Nothing
processCommand (Add x) store = 
  Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
processCommand (Get pos) store = getEntry pos store

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp =
  case parse inp of
       Nothing    => Just ("Invalid command\n", store)
       (Just cmd) => processCommand cmd store

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
