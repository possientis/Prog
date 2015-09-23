import java.io.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
import java.util.Random;

public class Test {

  // 'final' keyword for constant
  private static final double PI = 3.14159;

  // object passed by reference
  private static void printFiveValue(Incrementor inc){
    System.out.println(inc.nextValue());
    System.out.println(inc.nextValue());
    System.out.println(inc.nextValue());
    System.out.println(inc.nextValue());
    System.out.println(inc.nextValue());
  }

  public static void main(String[] args) throws IOException {

    Incrementor c = new Incrementor(10);
    printFiveValue(c);
    System.out.println(c.toString());
    System.out.println(c.toString());
    System.out.println(c.toString());
    System.out.println(c.toString());



  }


}
