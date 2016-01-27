// this was also done in PHP using traits
public class AbstractTraits {
  public static void main(String[] args){

    MyHelloWorld w = new MyHelloWorld(" world!");
    w.sayHelloWorld();

    // goes beyond php fragment here
    Hello h = () -> " dude, lambdas are cool";
    h.sayHelloWorld();

    
  }
}

@FunctionalInterface
interface Hello {
  public default void sayHelloWorld(){
    System.out.println("Hello" + getWorld());
  }
  public String getWorld();
}

class MyHelloWorld implements Hello {
  private final String world;
  public MyHelloWorld(String world){ this.world = world; }
  @Override
  public String getWorld(){ return this.world; }
}

