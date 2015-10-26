import java.io.*;
import java.util.*;
//import java.awt.event.*;
//import javax.swing.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

// contrived example of nested monitor lock out
public class BuggyLock {

  protected Object mMonObj = new Object();
  protected boolean mLocked = false;

  public synchronized void lock() throws InterruptedException{
    while(mLocked){
      synchronized(mMonObj){//The BuggyLock monitor lock is still held here
        mMonObj.wait(); // goes to sleep while holding BuggyLock
        // so unlock() below (synchronized) can never be called
      }
    }

    mLocked = true;
  }

  public synchronized void unlock(){
    mLocked = false;
    synchronized(mMonObj){
      mMonObj.notify();
    }
  }





  public static void main(String[] args) {

    System.out.println("Done!");
  }
}
