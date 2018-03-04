{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}



import qualified Data.Text as T
import Database.PostgreSQL.Simple.SqlQQ (sql)
import qualified Database.PostgreSQL.Simple as SQL
import Database.PostgreSQL.Simple.FromRow (FromRow (..), field)




data Book = Book
    { id_       :: Int
    , title     :: T.Text
    , author_id :: Int 
    } deriving (Show)

instance FromRow Book where
    fromRow = Book <$> field <*> field <*> field

creds :: SQL.ConnectInfo
creds = SQL.defaultConnectInfo
    { SQL.connectUser = "john"
    , SQL.connectPassword = "john"
    , SQL.connectDatabase = "library"
    }

-- requires QuasiQuotes
selectBooks :: SQL.Query
selectBooks = [sql|
    select 
        books.id,
        books.title,
        books.author_id
    from books
    |]

main :: IO ()
main = do
    conn  <- SQL.connect creds
    books <- SQL.query_ conn selectBooks :: IO [Book]
    print books
