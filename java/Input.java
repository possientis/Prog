import java.io.*;
import java.util.*;

public class Input {
  public static void main(String[] args) {

    Scanner sc = new Scanner(System.in);
    System.out.println("Priting the file passed in:");
    //int n1 = keyboard.nextInt();
    //int n2 = keyboard.nextInt();
    while(sc.hasNextLine()) System.out.println(sc.nextLine());
  }
}
