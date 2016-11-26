class Fibonacci {

  static void calcSequence() {

    long fiboNum = 1;

    long a = 1;

    long b = 1;

    for(;;) {

      fiboNum = a + b;

      a = b;

      b = fiboNum;

//      System.out.println(fiboNum);

    }
  }

  /*
  public static void main(String[] args) {
    
    calcSequence();

  }
  */
}

