import Database.HDBC
import Database.HDBC.PostgreSQL

main = do
  conn <- connect
  createTable conn
  insert conn
  deleteTable conn
  disconnect conn
  putStrLn "Disconnected from PostgreSQL server."
  return ()


connect :: IO Connection
connect = do
  conn <- connectPostgreSQL "host=localhost dbname=test user=john password=john"
  putStrLn "Connected to PostgreSQL server succesfully."
  return conn


createTable :: Connection -> IO ()
createTable conn = do
  let sql =   "CREATE   TABLE COMPANY " ++
              "(ID      INT PRIMARY KEY NOT NULL," ++
              " NAME    TEXT            NOT NULL," ++
              " AGE     INT             NOT NULL," ++
              " ADDRESS CHAR(50)                ," ++
              " SALARY  REAL                    )" 
  run conn sql []
  commit conn
  putStrLn "Created table 'COMPANY'"
  return ()
  
deleteTable :: Connection -> IO ()
deleteTable conn = do
  let sql = "DROP TABLE COMPANY"
  run conn sql []
  commit conn
  putStrLn "Delete table 'COMPANY'"
  return ()

insert :: Connection -> IO ()
insert conn = do
  let sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
          ++ "VALUES (1, 'Paul', 32, 'California', 20000.00 );"
  run conn sql []
  
  let sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
          ++ "VALUES (2, 'Allen', 25, 'Texas', 15000.00 );"
  run conn sql []

  let sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
          ++ "VALUES (3, 'Teddy', 23, 'Norway', 20000.00 );"
  run conn sql []

  let sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
            ++ "VALUES (4, 'Mark', 25, 'Rich-Mond ', 65000.00 );"
  run conn sql []

  commit conn
  putStrLn "Data was inserted into the table 'COMPANY'"
  return ()



 



