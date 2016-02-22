// medium quality random number generator suitable for testing
public class XorShift {
  public int getSeed(){
    return (this.hashCode() ^ (int)System.nanoTime());
  }
  public static int xorShift(int y) {
    y ^= (y << 6);
    y ^= (y >>> 21);  // unsigned right shift 
    y ^= (y << 7);
    return y;
  }
}
