import java.util.concurrent.atomic.*;
//import java.io.*;
//import java.util.*;
//import java.awt.event.*;
//import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Atomic {

  public static void main(String[] args){


    AtomicLong count = new AtomicLong();
    System.out.println(count.get());
    count.incrementAndGet();
    System.out.println(count.get());

  }
}
