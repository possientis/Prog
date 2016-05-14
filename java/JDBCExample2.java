// $ psql test to access test DB
// \dt for list of existing tables
// DROP TABLE COMPANY; to delete table so this code can run in full

import java.sql.*;
//import java.sql.Connection;     // Connection class
//import java.sql.DriverManager;  // DriverManager class
//import java.sql.SQLException;   // SQLException class
//import java.sql.Statement;      // Statement class
//import java.sql.ResultSet;      // hmmm.....

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
    try {
        conn.setAutoCommit(false);
    } catch (SQLException e){
      System.err.println("Failed to set auto commit to false");
    }

    createTableExample(conn);
    insertExample(conn);
    queryExample(conn);

    updateExample(conn);

    queryExample(conn);

    deleteExample(conn);

    queryExample(conn);

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

  public static void createTableExample(Connection conn){
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
  
  public static void insertExample(Connection conn){
    if(conn == null){
      System.err.println("insertExample: connection argument is null");
      System.exit(0);
    }
    Statement stmt = null;
    try {
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

    } catch (Exception e){
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );
      System.exit(0);
    }

    System.out.println("Records were created succesfully ...");

  }

  public static void queryExample(Connection conn){
    if(conn == null){
      System.err.println("insertExample: connection argument is null");
      System.exit(0);
    }
    Statement stmt = null;
    try {
      stmt = conn.createStatement();
      ResultSet rs = stmt.executeQuery( "SELECT * FROM COMPANY;" );
      while ( rs.next() ) {
        int id = rs.getInt("id");
        String  name = rs.getString("name");
        int age  = rs.getInt("age");
        String  address = rs.getString("address");
        float salary = rs.getFloat("salary");
        System.out.println( "ID = " + id );
        System.out.println( "NAME = " + name );
        System.out.println( "AGE = " + age );
        System.out.println( "ADDRESS = " + address );
        System.out.println( "SALARY = " + salary );
        System.out.println();
      }
      rs.close();
      stmt.close();
    } catch (Exception e) {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );
      System.exit(0);
    }
  }

  public static void updateExample(Connection conn){
    if(conn == null){
      System.err.println("insertExample: connection argument is null");
      System.exit(0);
    }
    Statement stmt = null;
    try {
      stmt = conn.createStatement();
      String sql = "UPDATE COMPANY set SALARY = 25000.00 where ID=1;";
      stmt.executeUpdate(sql);
      conn.commit(); 
    } catch (Exception e) {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );
      System.exit(0);
    }

    System.out.println("record updated succesfully ...");
  }

  public static void deleteExample(Connection conn){
    if(conn == null){
      System.err.println("insertExample: connection argument is null");
      System.exit(0);
    }
    Statement stmt = null;
    try {
      stmt = conn.createStatement();
      String sql = "DELETE from COMPANY where ID=2;";
      stmt.executeUpdate(sql);
      conn.commit();
    } catch (Exception e) {
      System.err.println( e.getClass().getName() + ": " + e.getMessage() );
      System.exit(0);
    }
    System.out.println("record deleted succesfully ...");
  }
}

