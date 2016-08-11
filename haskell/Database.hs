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
  putStrLn "connected to PostgreSQL server"
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
  putStrLn "created table 'COMPANY'"
  return ()
  
deleteTable :: Connection -> IO ()
deleteTable conn = do
  let sql = "DROP TABLE COMPANY"
  run conn sql []
  commit conn
  putStrLn "deleted table 'COMPANY'"
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

  let sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
            ++ "VALUES (?,?,?,?,?);"
  run conn sql [toSql (5::Int), 
                toSql "Mark", 
                toSql (43::Int), 
                toSql "New York", 
                toSql (32000::Double)]

  commit conn
  putStrLn "inserted data into table 'COMPANY'"
  return ()



 



