// example of conditional compilation based on final boolean variable
// One can check that this is indeed a case of conditional compilation
// by check the corresponding bytecodes:
// $ javap -c CondCompile.class

class CondCompile {

  public static void main(String[] args){

    if(AntHill.debug) { // determined at compile time

      System.out.println("Debug is true!");

    }
  }
}
