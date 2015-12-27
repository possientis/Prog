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

  }

  public synchronized int getNext(){
    return nextValue++;
  }

  private int nextValue = 0;

}

