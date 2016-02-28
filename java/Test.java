import java.util.concurrent.*;

public class Test {

  public static void main(String[] args) {
    int total = 0;

    for(int i = 0; i < 10 ; ++i){
      final int j = i;
      (new Thread(()-> {
        System.out.println(j+ ":" + total);})).start();
    }

  }
}
