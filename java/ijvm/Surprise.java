class Surprise {

  static boolean surpriseTheProgrammer(boolean bVal) {

    while(bVal)
    {
      try
      {
        return true;
      }
      finally
      {
        break;
      }
    }

    return false;

  }

  public static void main(String[] args) {

    System.out.println(surpriseTheProgrammer(true));    // false
    System.out.println(surpriseTheProgrammer(false));   // false

  }

}


