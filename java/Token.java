import java.io.*;
import java.util.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Token {


  public static void main(String[] args) {


    String line = "This is a line for, a string tokenizer";
    StringTokenizer tokenizer = new StringTokenizer(line, ", ");

    while(tokenizer.hasMoreTokens()){

      String next = tokenizer.nextToken();
      System.out.println(next);

    }


  }



}
