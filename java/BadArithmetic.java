class BadArithmetic {

  public static void main(String[] args)
  {
    byte a = 0x01;
    byte b = 0x01;

  //  byte c = a + b; // will not compile

    System.out.println("c = " + (byte) (a + b));
  }

  static byte addOneAndOne(){

    byte a = 0x01;
    byte b = 0x01;
    byte c = (byte) (a + b);
    return c;
  }



}
