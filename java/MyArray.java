import java.io.*;
import java.util.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class MyArray {


  public static void main(String[] args) throws IOException {

    int[] myArr = new int[5];
    for(int i = 0; i < 5; ++i){
      myArr[i] = i;
      System.out.println(myArr[i]);
    }

    // ArrayList is a template
    ArrayList<String> strList = new ArrayList<String>();

    //String str1 = "hello";
    strList.add("hello");
    strList.add("how are you?");
    System.out.println(strList.size());
    System.out.println(strList.get(0));
    System.out.println(strList.get(1));
  }

}
