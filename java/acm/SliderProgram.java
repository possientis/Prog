// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import java.awt.event.*;
import acm.util.*;
import javax.swing.*;

public class SliderProgram extends GraphicsProgram {

  public void run() {
    JButton button = new JButton("Slide");

    add(button, SOUTH);
    addActionListeners();
  }

  public void actionPerformed(ActionEvent e){

    String cmd = e.getActionCommand();
    if(cmd.equals("Slide")){  // create new slider
      Slider slider = new Slider(SIZE, rgen.nextColor());
      add(slider,0,rgen.nextDouble(0,600));

      // run the slider on a new thread
      Thread sliderThread = new Thread(slider);
      sliderThread.start();
    }
  }


  private static final int SIZE = 20;
  private RandomGenerator rgen = RandomGenerator.getInstance();

}

