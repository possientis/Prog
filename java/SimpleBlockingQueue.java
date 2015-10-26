import java.io.*;
import java.util.*;
import java.util.concurrent.*;
//import java.awt.event.*;
//import javax.swing.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public abstract class SimpleBlockingQueue<E> implements BlockingQueue<E> {

  private List<E> mList;
  private int mCapacity;
  private boolean isFull(){
    return mList.size() >= mCapacity;
  }

  // you do not need a lock on the constructor (why?)
  public SimpleBlockingQueue(int capacity){
    mList = new ArrayList<E>();
    mCapacity = capacity;
  }

  public synchronized E take() throws InterruptedException{
    
    // rule of thumb: always call wait in a loop.
    // wait() puts yourself to sleep. A notify or notifyAll called
    // by another thread will wake you up. However, you could
    // imagine a situation when a notify has been issued for other
    // reasons than the queue no longer being empty. or that for some
    // reason another thread has just emptied the queue. So you 
    // want to re-test condition before proceeding.
    while(mList.isEmpty()){
      wait();
    }

    final E e = mList.remove(0);

    notifyAll();

    return e;
  }



  public static void main(String[] args) {

    System.out.println("Done!");
  }

}
