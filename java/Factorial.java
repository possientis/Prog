import java.io.*;

public class Factorial {

  private static final int MAX_NUM = 25;

  private static long fact(int n){

    long result = 1;

    for(int i = 1; i <= n; ++i)
      result *= i;

    return result;
  }

  public static void main(String[] args) {

    for(int i = 0; i <= MAX_NUM; ++i)
      System.out.println(i + "! = " + fact(i));

  }



}
