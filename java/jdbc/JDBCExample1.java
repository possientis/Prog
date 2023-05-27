import java.sql.DriverManager;
import java.sql.Connection;
import java.sql.SQLException;

// java -cp .:/usr/share/java/postgresql.jar JDBCExample1

public class JDBCExample1 {

  public static void main(String[] args) {

    final String user = args[0];

    System.out.println("PostgreSQL jdbc connection testing ...");

    try {
      
      Class.forName("org.postgresql.Driver");

    } catch (ClassNotFoundException e){

      System.out.println("Cannot find PostgreSQL jdbc driver.");

      e.printStackTrace(); 

      System.exit(1);
    }

    System.out.println("PostgreSQL jdbc driver is registered!");

    Connection connection = null;

    try {

      final String dbname = "jdbc:postgresql://127.0.0.1/" + user;

      final String username = user;

      final String password = user;

      connection = DriverManager.getConnection(dbname, username, password);

    } catch (SQLException e) {

      System.out.println("Connection Failed! Check output console");

      e.printStackTrace();

      System.exit(1);

    }

    if (connection != null) {

      System.out.println("You made it, take control your database now!");

      System.exit(0);

    } else {

       System.out.println("Failed to make connection!");

       System.exit(1);
    }
  }
}
