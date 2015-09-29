import java.io.*;
import java.util.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class ReadFile {


  public static void main(String[] args) {

    try
    {

      FileReader file = new FileReader("Test.java");

      BufferedReader reader = new BufferedReader(file);

      while(true){

        String line = reader.readLine();
        if(line == null) break;
        System.out.println(line);

      }

      reader.close();
    }
    catch(FileNotFoundException e)
    {
      System.err.println("File not found");

    }
    catch(IOException e)
    {
      System.err.println("Unable to read file");
    }

  }
}
