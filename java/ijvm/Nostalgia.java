class Nostalgia {
    
  static int giveMeThatOldFashionedBoolean(boolean bVal) {

    try
    {
      if(bVal) {
        return 1;
      }

      return 0;

    }
    finally 
    {
      System.out.println("Got old fashioned.");
    }

  }

  public static void main(String[] args) {

    System.out.println(giveMeThatOldFashionedBoolean(true));
    System.out.println(giveMeThatOldFashionedBoolean(false));

  }
}
