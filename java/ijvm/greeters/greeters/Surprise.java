import org.artima.greeter.Greeter;

public class Surprise implements Greeter {

  public void greet() {

    // Choose one of four greeters pseudo-randomly and
    // invoke its greet() method.
    
    int choice = (int) (Math.random() * 3.99);

    Greeter g;

    switch(choice) {

      case 0:

        g = new Hello();

        g.greet();

        break;

      case 1:

        g = new Greetings();

        g.greet();

        break;

      case 2:

        g = new Salutations();

        g.greet();

        break;

      case 3:

        g = new HowDoYouDo();

        g.greet();

        break;
    }
  }
}
