class Example6 {

  private int width = 3;
  // Constructor one:
  // This constructor begins with a this() constructor invocation,
  // which gets compiled to a same-class <init() method
  // invocation.
  Example6() {
    this(1);
    System.out.println("Example6(), width = " + width);
  }

  // Constructor two:
  // This constructor begins with no explicit invocation of another
  // constructor, so it will get compiled to an <init() method
  // that begins with an invocation of the superclass's no-arg
  // <init() method.
  Example6(int width) {
    this.width = width;
    System.out.println("Example6(int), width = " + width);
  }

  // Constructor three:
  // This constructor begins with super(), an explicit invocation
  // of the superclass's no-arg constructor. Its <init() method
  // will begin with an invocation of the superclass's no-arg
  // <init() method.
  Example6(String msg) {
    super();
    System.out.println("Example6(String), width = " + width);
    System.out.println(msg);
  }

  public static void main(String[] args) {
    String msg = "The Agapanthus is also known as Lilly of the Nile.";
    Example6 one = new Example6();
    Example6 two = new Example6(2);
    Example6 three = new Example6(msg);
  }
}

