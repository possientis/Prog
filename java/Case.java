import java.io.*;
//import java.util.List;
//import java.util.ArrayList;

public class Case {

  // 'final' keyword for constant
  private static final double PI = 3.14159;

  public static void main(String[] args) throws IOException {

    int x = 5;
    int y = 0;

    switch(x){
      case 0:
        y = 0;
        break;
      case 1:
        y = 1;
        break;
      default:
        y = 5;
        break;
    }
        System.out.println(y);
  }
}
