import java.io.*;
import java.util.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Test {


  public static void main(String[] args) throws IOException {


    FileReader file = new FileReader("Test.java");
    BufferedReader reader = new BufferedReader(file);

    while(true){

      String line = reader.readLine();
      if(line == null) break;
      System.out.println(line);

    }

    reader.close();
  }




}
