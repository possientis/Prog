import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Foreach {

  public static void main(String[] args){



    List<String> list = new ArrayList<String>(3);
    list.add("abc");
    list.add("def");
    list.add("ghi");

    for(String s: list){
      System.out.println(s);
    }

    System.out.println("Done!");

  }
}
