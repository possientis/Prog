// This code does not work yet
import java.io.*;
import java.util.List;
import java.util.ArrayList;

public class Fib {

  public static void main(String[] args) {

    //System.out.println("Hello, World");

  }

  public static List<Integer>fib(int n){

    List<Integer> seq = new ArrayList(n);

    seq[0] = 1;
    seq[1] = 1;

    for(int i = 2; i < n; ++i){
      seq[i] = seq[i-2] + seq[i-1];
    }

    return seq;
  }
}
