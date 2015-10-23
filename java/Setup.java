import java.io.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class Setup {


  public static void main(String[] args) throws IOException {

    Runnable myRunnable = new Runnable(){
      public void run(){
        A a = new A(3);
        B b = new B(5);

        System.out.println("This is running");
        System.out.println(a.a);
        System.out.println(b.b);
      }};

    new Thread(myRunnable).start();

  }
}

class A {
  int a;
  A(int a){this.a = a;}
}

class B {
  int b;
  B(int b){this.b = b;}
}
