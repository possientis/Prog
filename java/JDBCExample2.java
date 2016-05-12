import java.sql.Connection;     // Connection class
import java.sql.DriverManager;  // DriverManager class
import java.sql.SQLException;   // SQLException class
import java.sql.Statement;

// DO NOT FORGET after compiling
// java -cp .:/usr/share/java/postgresql-jdbc4.jar JDBCExample2

public class JDBCExample2 {

  // port 5432 seems to be default port for postgresql. Its inclusion in url
  // seems to be optional here. It is not clear why connection seems to be
  // succesful, regardless of ufw settings.
  private static final String url = "jdbc:postgresql://127.0.0.1:5432/test";
  private static final String user = "john";
  private static final String password = "john";

  public static void main(String[] args){
    Connection conn = connect();

    createCompanyTable(conn);

    
    try {
      conn.close();
    } catch (SQLException e){
      System.err.println("Failed to close database, ignoring...");
    }

  }

  public static Connection connect() {
    Connection conn = null;
    try {
      conn = DriverManager.getConnection(url, user, password);
      System.out.println("Connected to PostgreSQL server succesfully.");
    } catch (SQLException e){
      System.err.println(e.getMessage());
    }

    return conn;
  }

  public static void createCompanyTable(Connection conn){
    if(conn == null){
      System.err.println("createCompanyTable: connection argument is null");
      System.exit(0);
    }
    Statement stmt = null;
    try {
      stmt = conn.createStatement();
      String sql =  "CREATE   TABLE COMPANY " +
                    "(ID      INT PRIMARY KEY NOT NULL," +
                    " NAME    TEXT            NOT NULL," +
                    " AGE     INT             NOT NULL," +
                    " ADDRESS CHAR(50)                ," +
                    " SALARY  REAL                    )" ;
      stmt.executeUpdate(sql);
      stmt.close();
    } catch (Exception e){
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );
      System.exit(0);
    }

    System.out.println("Table created succesfully");

  }



}
