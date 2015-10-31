import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Race {

  private static int c = 0;



  public static void main(String[] args) throws InterruptedException{


    Runnable run1 = new Runnable(){
      public void run(){
        c = 1;
        }
      };

    Runnable run2 = new Runnable(){
      public void run(){
        c = 2;
        }
      };


    Thread t1 = new Thread(run1);
    Thread t2 = new Thread(run2);

    t1.start();
    t2.start();

    t1.join();
    t2.join();

    System.out.println("c = " + c);
    System.out.println("Done!");



  }
}
