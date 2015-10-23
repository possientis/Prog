import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class ThreadEx {

  public static void main(String[] args) {

    //System.out.println(Runtime.getRuntime().availableProcessors());
    Thread a = new MyThread();
    a.start();

    Runnable run1 = new Runnable(){
      public void run(){
        System.out.println("This is also running");
      }
    };

    Thread b = new Thread(run1);
    b.start();

    Runnable run2 = new MyRunnable();
    Thread c = new Thread(run2);
    c.start();

    try{  // needed, or else need to declare possible exception
    a.join();
    b.join();
    c.join();
    }
    catch(InterruptedException e){
      //
    }

    System.out.println("All children threads are complete");


  }
}

class MyThread extends Thread{
  public void run(){
    System.out.println("Thread is running");
  }
}

class MyRunnable implements Runnable {
  public void run(){
    System.out.println("and this is yet another thread running");
  }
}
