import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Pascal{

  public static void main(String[] args){

    List<Integer> list = pascal(1);
    System.out.println(list.toString());

  }

  public static List<Integer> pascal(int n){

    if(n == 1){
      List<Integer> list = new ArrayList<Integer>();
      list.add(1);
      return list;
    }
    else{
      return addList(shiftLeft(pascal(n -1)),shiftRight(pascal(n -1)));
    }
  }

  public static List<Integer> shiftLetf(List<Integer> list){

    return list;

  }


}
