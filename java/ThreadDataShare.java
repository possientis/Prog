import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class ThreadDataShare {

  public static void main(String[] args) throws InterruptedException{

    int a = 5;

    Thread t = new Thread(){
      public void run(){
        System.out.println("Thread t: a = " + a);
      }
    };

    t.join();

    Thread s = new Thread(() -> {System.out.println("Thread s: a = " + a);});

    t.start();
    s.start();

  }
}
