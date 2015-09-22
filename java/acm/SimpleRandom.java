// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import acm.util.*;

public class SimpleRandom extends ConsoleProgram {

  private RandomGenerator rgen = RandomGenerator.getInstance();

  public void run() {

    // deterministic for debug
    rgen.setSeed(1);

    for(int i = 0; i < 10; ++i)
    {
      int dieRoll = rgen.nextInt(1,6);
      println("You rolled " + dieRoll);
    }

  }

}

