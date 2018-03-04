{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import qualified Database.PostgreSQL.Simple as SQL


creds :: SQL.ConnectInfo
creds = SQL.defaultConnectInfo
    { SQL.connectUser = "john"
    , SQL.connectPassword = "john"
    , SQL.connectDatabase = "library"
    }


selectBooks :: SQL.Connection -> IO [(Int,T.Text,Int)]
selectBooks conn = SQL.query_ conn "select id, title, author_id from books"


main :: IO ()
main = do
    conn  <- SQL.connect creds
    books <- selectBooks conn
    print books




