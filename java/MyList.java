import java.util.List;
import java.util.ArrayList;

public class MyList {

  public static void main(String[] args) {

    //System.out.println("Hello, World");

  }

  public static List<Integer>fib(Integer n){

    List<Integer> seq = new ArrayList(n);

    seq[0] = 1;
    seq[1] = 1;

    for(Integer i = 2; i < n; ++i){
      seq[i] = seq[i-2] + seq[i-1];
    }

    return seq;
  }
}
