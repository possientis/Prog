class Example7 {
  public static void main(String[] args) {
    Dog dog = new CockerSpaniel();
    dog.sayHello();


    Friendly fr = (Friendly) dog;
    // Invoke sayGoodbye() on a CockerSpaniel object through a
    // reference of type Friendly.
    fr.sayGoodbye();


    fr = new Cat();
    // Invoke sayGoodbye() on a Cat object through a reference
    // of type Friendly.
    fr.sayGoodbye();

  }
}
