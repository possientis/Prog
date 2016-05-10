import java.sql.Connection;     // Connection class
import java.sql.DriverManager;  // DriverManager class
import java.sql.SQLException;   // SQLException class

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
  }

  public static Connection connect(){
    Connection conn = null;
    try {
      conn = DriverManager.getConnection(url, user, password);
      System.out.println("Connected to PostgreSQL server succesfully.");
    } catch (SQLException e){
      System.out.println(e.getMessage());
    }

    return conn;
  }
}
