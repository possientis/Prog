class Example2 {

  // Invoking main is an active use of Example2
  public static void main(String[] args){

    // Using hoursOfSleep is an active use of NewParent, but a
    // passive use of NewbornBaby

    int hours = NewbornBaby.hoursOfSleep;

    System.out.println(hours);

  }

  static {

    System.out.println("Example2 was initialized");

  }

}
