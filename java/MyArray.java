import java.io.*;
import java.util.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class MyArray {


  public static void main(String[] args) throws IOException {

    int[] myArr = new int[5];
    int[][] matrix = new int[2][3];

    ArrayList<Integer> intList = new ArrayList<Integer>();
    intList.add(5);

    // ArrayList is a template
    ArrayList<String> strList = new ArrayList<String>();

    readList(strList);

    for(int i = 0; i < strList.size(); ++i){

      System.out.println(strList.get(i));
    }

  }


  private static void readList(ArrayList<String> list){
    // does nothing for now
    list.add("hello");
  }

}
