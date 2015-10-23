import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class PingPong {




  public static void main(String[] args) {


    Runnable run1 = new Runnable(){
      public void run(){
        for(int i = 0; i < 5; ++i){
          System.out.println("ping");
        }
      }};

    Runnable run2 = new Runnable(){
      public void run(){
        for(int i = 0; i < 5; ++i){
          System.out.println("pong");
        }
      }};


    Thread t1 = new Thread(run1);
    Thread t2 = new Thread(run2);

    t1.start();
    t2.start();

    try{

      t1.join();
      t2.join();
    }
    catch(InterruptedException e){
      System.out.println("An exception was thrown");
    }


    System.out.println("Done!");



  }
}
