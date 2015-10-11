import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class MyThread {


  public static void main(String[] args) throws IOException {

    MyRunnable X = new MyRunnable();

    Thread t = new Thread(X);

    t.start();

  }
}
