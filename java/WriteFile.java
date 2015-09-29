import java.io.*;
import java.util.*;
import java.nio.file.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class WriteFile {


  public static void main(String[] args) throws IOException {


    PrintWriter writer = new PrintWriter("log","UTF-8");
    writer.println("Hello World");
    writer.println("This is a second line");

    writer.close();


  }
}
