import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Test {


  public static void main(String[] args) throws IOException {


    Runnable myRunnable = new Runnable(){
      public void run(){
        System.out.println("This is running");
      }};

    new Thread(myRunnable).start();


  }
}
