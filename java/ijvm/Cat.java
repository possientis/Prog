class Cat implements Friendly {

  public void eat() {
    System.out.println("Chomp, chomp, chomp.");
  }

  public void sayHello() {
    System.out.println("Rub, rub, rub.");
  }

  public void sayGoodbye() {

    System.out.println("Scamper.");
  }

  protected void finalize() {

    System.out.println("Meow!");

  }
}
