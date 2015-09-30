// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import acm.util.*;

public class Test extends GraphicsProgram {

  private static final RandomGenerator rgen = RandomGenerator.getInstance();
  public void run() {


    GOval[] circles = new GOval[20];

    for(int i = 0; i < 20; ++i){

      circles[i] = new GOval(100 + i*10,100 + i*10, 50, 50);
      add(circles[i]);
    }

  }
}

