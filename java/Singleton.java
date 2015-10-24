import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

// random code, many things are bound to be wrong
public class Singleton {

  private static volatile Singleton inst_ = null;
  private static int count_ = 0;

  public static Singleton instance(){

    count_++;
    Singleton result = inst_;
    if(result == null){
      synchronized(Singleton.class)
      {
        result = inst_;
        if (result == null)
        {
          result = new Singleton();
          inst_ = result;
        }
      }
    }

    return result;
  }

  public void displayCounter(){
    System.out.println(instance().count_);
  }


  public static void main(String[] args) throws IOException, InterruptedException {


    Runnable run1 = new Runnable(){

      public void run(){
        System.out.println("First thread is running");
        Singleton a = new Singleton();
        a.displayCounter();
        System.out.println("First thread is terminating");

        }
      };

    Runnable run2 = new Runnable(){
      public void run(){

        System.out.println("Second thread is running");
        Singleton b = new Singleton();
        b.displayCounter();
        System.out.println("Second thread is terminating");

        }
      };


    Thread t1 = new Thread(run1);
    Thread t2 = new Thread(run2);

    t1.start();
    t2.start();

    t1.join();
    t2.join();

    System.out.println("Done!");



  }
}
