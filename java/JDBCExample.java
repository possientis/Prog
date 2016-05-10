import java.sql.DriverManager;
import java.sql.Connection; // Connection class
import java.sql.SQLException;

// Eventhough the postgresql-jdbc4.jar is placed in the usual 
// directory /usr/share/java, you still need to spell it out 
// when running the program (add the jar to your classpath)
// Do not forget the '.:' when specifiying the -cp option. 

// java -cp .:/usr/share/java/postgresql-jdbc4.jar JDBCExample

public class JDBCExample {
  public static void main(String[] args){
    System.out.println("PostgreSQL jdbc connection testing ...");

    try {
      
      Class.forName("org.postgresql.Driver");

    } catch (ClassNotFoundException e){

      System.out.println("Cannot find PostgreSQL jdbc driver.");
      e.printStackTrace(); 
      return;
    }

    System.out.println("PostgreSQL jdbc driver is registered!");

    Connection connection = null;

    try {

      connection = DriverManager.getConnection(
          "jdbc:postgresql://127.0.0.1/test", "john", "john");

    } catch (SQLException e) {

      System.out.println("Connection Failed! Check output console");
      e.printStackTrace();
      return;

    }

    if (connection != null) {
      System.out.println("You made it, take control your database now!");
    } else {
       System.out.println("Failed to make connection!");
    }
  }
}
