import Database.HDBC
import Database.HDBC.PostgreSQL

main = do
  conn <- connect
  createTable conn
  insertInTable conn
  readFromTable conn
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

insertInTable :: Connection -> IO ()
insertInTable conn = do
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
  -- prepare :: IConnection conn => conn -> String -> IO Statement
  stmt <- prepare conn sql  -- compiles sql statement first  
  -- execute :: Statement -> [SqlValue] -> IO Integer
  execute stmt []           -- then execute
  -- executeMany :: Statement -> [[SqlValue]] -> IO () 
  -- may be useful ....


  let sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
            ++ "VALUES (?,?,?,?,?);"
  run conn sql [toSql (5::Int), 
                toSql "Thomas", 
                toSql (43::Int), 
                toSql "New York", 
                toSql (32000::Double)]

  commit conn
  putStrLn "inserted data into table 'COMPANY'"
  return ()

readFromTable :: Connection -> IO () 
readFromTable conn = do
  let sql = "SELECT * FROM COMPANY;"
  putStrLn "reading data from table 'COMPANT'" 
  -- quickQuery :: IConnection conn => conn -> String -> [SqlValue] -> IO [[SqlValue]]
  -- alternatively, use 'prepare' then 'execute' then call 'fetchAllRows' on Statement obj
  -- or 'fetchAllRowsAL' or 'fetchRow' (one row at a time)
  result <- quickQuery conn sql []
  let out = foldr (\x -> \y -> (show x) ++ "\n" ++ y) [] result 
  putStrLn out
  return ()

 



