import java.io.*;
import java.util.Scanner;

public class AddIntegers {
  public static void main(String[] args) {

    Scanner keyboard = new Scanner(System.in);
    System.out.println("This program adds two numbers.");
    System.out.print("Enter n1: ");
    int n1 = keyboard.nextInt();
    System.out.print("Enter n2: ");
    int n2 = keyboard.nextInt();
    int total = n1 + n2;
    System.out.println("The total is " + total + ".");
  }
}
