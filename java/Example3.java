class Example3 {
  // Invoking main() is an active use of Example3
  public static void main(String[] args) {
  // Using Angry.greeting is a passive use of Angry
  System.out.println(Angry.greeting);
  // Using Dog.greeting is a passive use of Dog
  System.out.println(Dog.greeting);
  }

  static {
    System.out.println("Example3 was initialized.");
  }
}
