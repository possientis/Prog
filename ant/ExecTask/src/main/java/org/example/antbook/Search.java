package org.example.antbook;


public class Search {
  public static void main(String args[]) throws Exception {

    if(args.length!=2) {
      System.out.println("search: index searchterm");
      System.exit(-1);
    }

    System.out.println("first argument: " + args[0]);
    System.out.println("second argument: " + args[1]);
    
  }
}
