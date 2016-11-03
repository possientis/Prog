class Dog {
  static final String greeting = "Woof, woof, world!";
  static {
    System.out.println("Dog was initialized.");
  }
  static int getAngerLevel() {
    System.out.println("Anger was initialized");
    return 1;
  }
}
