class CockerSpaniel extends Dog implements Friendly {
  // How many times this Cocker Spaniel woofs when saying hello.
  private int woofCount = ((int) (Math.random() * 4.0)) + 1;

  // How many times this Cocker Spaniel wimpers when saying
  // goodbye.
  private int wimperCount = ((int) (Math.random() * 3.0)) + 1;
  
  public void sayHello() {
    // Wag that tail a few times.
    super.sayHello();

    System.out.print("Woof");

    for (int i = 0; i < woofCount; ++i) {
      System.out.print(", woof");
    }

    System.out.println("!");
  }

  public void sayGoodbye() {

    System.out.print("Wimper");

    for (int i = 0; i < wimperCount; ++i) {
      System.out.print(", wimper");
    }

    System.out.println(".");

  }
}
