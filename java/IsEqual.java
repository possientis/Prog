public class IsEqual{
  public static void main(String[] args){
    System.out.println(isEqual1(42,42));    // true
    System.out.println(isEqual2(42,42));    // true
    Integer x = new Integer(42);
    Integer y = new Integer(42);
    System.out.println(isEqual2(x,y));      // false 
  }

  private static boolean isEqual1(int x, int y){
      return x == y;
  }

  private static boolean isEqual2(Integer x, Integer y){
    return x == y;
  }
}
