// operators | & << >> >>> expect ints

public class Byte {
  public static void main(String[] args){

    byte a = (byte) 0xFF;
    System.out.println(a);        // -1 (implicite conversion to int)

    int x = a & 0xFF; 
    System.out.println(x);        // 255

    System.out.println(x << 1);   // 510
    System.out.println(x >> 1);   // 127
    System.out.println(x >>> 1);  // 127

    int y = (int) a;
    System.out.println(y);        // -1

    System.out.println(y << 1);   // -2 
    System.out.println(y >> 1);   // -1         (0xFFFF FFFF) 
    System.out.println(y >>> 1);  // 2147483647 (0x7FFF FFFF)

  }
}
