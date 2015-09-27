import java.io.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Character2 {


  public static void main(String[] args) throws IOException {

    String s = "Hello world!";
    char ch = s.charAt(0);
    System.out.println(Character.toUpperCase('a'));
    System.out.println(Character.isDigit('0'));
    System.out.println(Character.isLetter('£'));
    System.out.println(Character.isLetterOrDigit('d'));
    System.out.println(Character.isLowerCase('d'));
    System.out.println(Character.isUpperCase('d'));
    System.out.println(Character.isWhitespace('d')); // 'space' not 'Space'

  }



}
