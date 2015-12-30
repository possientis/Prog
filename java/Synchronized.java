import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Synchronized {

  public static void main(String[] args){

    Synchronized a = new Synchronized();
    System.out.println(a.getNext());
    System.out.println(a.getNext());
    System.out.println(a.getNext());
    System.out.println(a.getNext());
    System.out.println(a.lockNext());
    System.out.println(a.lockNext());
    System.out.println(a.lockNext());
    System.out.println(a.lockNext());


  }

  public synchronized int getNext(){
    return nextValue++;
  }

  public int lockNext(){
    synchronized(lock){
      lockValue++;
    }
    return lockValue;
  }



  private int nextValue = 0;
  private Object lock = new Object();
  private int lockValue = 0;

}

