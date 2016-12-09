
import java.sql.Connection;     
import java.sql.DriverManager;  
import java.sql.SQLException;   
import java.sql.Statement;      
import java.sql.ResultSet;      

// DO NOT FORGET after compiling
// java -cp /usr/share/java/postgresq.jar:. JDBCExample2

public class JDBCExample2 {

  // inclusion of port number in url seems to be optional
  private static final String url = "jdbc:postgresql://127.0.0.1:5432/john";
  private static final String user = "john";
  private static final String password = "john";

  public static void main(String[] args){

    Connection conn = connect();

    try 
    {
      conn.setAutoCommit(false);
    } 
    catch (SQLException e)
    {
      System.err.println("Failed to set auto commit to false");

      System.exit(1);
    }

    createTableExample(conn);

    insertExample(conn);

    queryExample(conn);

    updateExample(conn);

    queryExample(conn);

    deleteExample(conn);

    queryExample(conn);

    deleteTableExample(conn);

    try 
    {

      conn.close();

    } 
    catch (SQLException e)
    {
      System.err.println("Failed to close database");

      System.exit(1);
    }

  }

  public static Connection connect() {

    Connection conn = null;

    try 
    {
      conn = DriverManager.getConnection(url, user, password);

      System.out.println("Connected to PostgreSQL server successfully ...");
    } 
    catch (SQLException e)
    {
      System.err.println(e.getMessage());

      System.exit(1);
    }

    return conn;
  }

  public static void createTableExample(Connection conn){

    if(conn == null)
    {
      System.err.println("createTableExample: connection argument is null");

      System.exit(1);
    }

    Statement stmt = null;

    try 
    {
      stmt = conn.createStatement();

      String sql =  "CREATE   TABLE COMPANY " +
                    "(ID      INT PRIMARY KEY NOT NULL," +
                    " NAME    TEXT            NOT NULL," +
                    " AGE     INT             NOT NULL," +
                    " ADDRESS CHAR(50)                ," +
                    " SALARY  REAL                    );" ;

      stmt.executeUpdate(sql);

      stmt.close();

      conn.commit();
    } 
    catch (Exception e)
    {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );

      System.exit(1);
    }

    System.out.println("Table created successfully ...");

  }
  
  public static void insertExample(Connection conn){

    if(conn == null)
    {
      System.err.println("insertExample: connection argument is null");

      System.exit(1);
    }

    Statement stmt = null;

    try 
    {
      stmt = conn.createStatement();

      String sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
                   + "VALUES (1, 'Paul', 32, 'California', 20000.00 );";

      stmt.executeUpdate(sql);

      sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
            + "VALUES (2, 'Allen', 25, 'Texas', 15000.00 );";

      stmt.executeUpdate(sql);

      sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
            + "VALUES (3, 'Teddy', 23, 'Norway', 20000.00 );";

      stmt.executeUpdate(sql);

      sql = "INSERT INTO COMPANY (ID,NAME,AGE,ADDRESS,SALARY) "
            + "VALUES (4, 'Mark', 25, 'Rich-Mond ', 65000.00 );";

      stmt.executeUpdate(sql); 

      stmt.close();

      conn.commit();

    } 
    catch (Exception e)
    {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );

      System.exit(1);
    }

    System.out.println("Records were created successfully ...");

  }

  public static void queryExample(Connection conn){

    if(conn == null)
    {
      System.err.println("queryExample: connection argument is null");

      System.exit(1);
    }

    Statement stmt = null;

    try 
    {
      stmt = conn.createStatement();

      ResultSet rs = stmt.executeQuery( "SELECT * FROM COMPANY;" );

      while ( rs.next() ) 
      {
        int id = rs.getInt("id");

        String  name = rs.getString("name");

        int age  = rs.getInt("age");

        String  address = rs.getString("address");
        
        float salary = rs.getFloat("salary");

        System.out.println( 
          "ID: " + id +
          ",\tNAME: " + name +
          ",\tAGE: " + age +
          ",\tADDRESS: " + address.trim() +
          ",\tSALARY: " + salary 
        );
      }

      rs.close();

      stmt.close();

    } 
    catch (Exception e) 
    {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );

      System.exit(1);
    }
  }

  public static void updateExample(Connection conn){

    if(conn == null)
    {
      System.err.println("updateExample: connection argument is null");

      System.exit(1);
    }

    Statement stmt = null;

    try 
    {
      stmt = conn.createStatement();

      String sql = "UPDATE COMPANY set SALARY = 25000.00 where ID=1;";

      stmt.executeUpdate(sql);

      conn.commit(); 
    } 
    catch (Exception e) 
    {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );

      System.exit(1);
    }

    System.out.println("record updated successfully ...");
  }

  public static void deleteExample(Connection conn){

    if(conn == null)
    {
      System.err.println("deleteExample: connection argument is null");

      System.exit(1);
    }

    Statement stmt = null;

    try 
    {
      stmt = conn.createStatement();

      String sql = "DELETE from COMPANY where ID=2;";

      stmt.executeUpdate(sql);

      conn.commit();
    } 
    catch (Exception e) 
    {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );

      System.exit(1);
    }

    System.out.println("record deleted successfully ...");
  }

  public static void deleteTableExample(Connection conn){

    if(conn == null)
    {
      System.err.println("deleteTableExample: connection argument is null");

      System.exit(1);
    }

    Statement stmt = null;

    try 
    {
      stmt = conn.createStatement();

      String sql = "DROP TABLE company;";

      stmt.executeUpdate(sql);

      conn.commit();
    } 
    catch (Exception e) 
    {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );

      System.exit(1);
    }

    System.out.println("Table was deleted successfully ...");
  }
}

