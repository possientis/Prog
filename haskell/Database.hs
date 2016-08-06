import Database.HDBC
import Database.HDBC.PostgreSQL

main = do
  conn <- connectPostgreSQL "host=localhost dbname=test user=john password=john"
  putStrLn "Succesfully connected to database"
  disconnect conn
  return ()
