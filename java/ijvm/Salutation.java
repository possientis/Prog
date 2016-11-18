class Salutation {

  private static final String hello = "Hello, world!";
  private static final String greeting = "Greetings, planet!";
  private static final String salutation = "Salutations, orb!";

  private static int choice = (int) (Math.random() * 2.99);

  public static void main(String[] args) {
    String s = hello;

    if (choice == 1) {
      s = greeting;
    }
    else if (choice == 2) {
      s = salutation;
    }

    System.out.println(s);

  }
}
