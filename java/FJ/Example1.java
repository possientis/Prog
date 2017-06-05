class Example1  {

  public static void main(String[] args) {
    System.out.println("Example1 is running...");

    Object x = new Pair(new A(), new B()).setfst(new B());
    Object y = ((Pair) new Pair (new Pair(new A(), new B()), new A()).fst).snd;
  }
}

class A extends Object { A() { super(); } }

class B extends Object { B() { super(); } }

class Pair extends Object {
  Object fst;
  Object snd;
  // Constructor:
  Pair(Object fst, Object snd) {
    super(); this.fst = fst; this.snd = snd;
  }
  // Method definition
  Pair setfst(Object newfst) {
    return new Pair(newfst, this.snd);
  }
}





