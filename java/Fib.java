// This code does not work yet
import java.io.*;
import java.util.List;
import java.util.ArrayList;

public class Fib {

  public static void main(String[] args) {

    ArrayList<Integer> iList = fib(20);

    for(int i = 0; i < iList.size(); ++i){
      System.out.println(iList.get(i));
    }

  }

  public static ArrayList<Integer>fib(int n){

    ArrayList<Integer> seq = new ArrayList<Integer>();

    seq.add(0,1);
    seq.add(1,1);

    for(int i = 2; i < n; ++i){
      seq.add(i,seq.get(i-2) + seq.get(i-1));
    }

    return seq;
  }
}
