// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import java.awt.event.*;
import acm.util.*;
import javax.swing.*;

public class RacingProgram extends GraphicsProgram {

  public void run() {

    racers = new RacingSquare[NUM_RACERS];
    finished = new boolean[NUM_RACERS];
    threads = new Thread[NUM_RACERS];

    // finish line
    add(new GLine(510,0,510,600));

    add(new JButton("Start!"), SOUTH);
    addActionListeners();

  }

  public void actionPerformed(ActionEvent e){

    String cmd = e.getActionCommand();
    if(cmd.equals("Start!")){  // create new slider
      for(int i = 0; i < NUM_RACERS; ++i){
        if(racers[i] != null){
          remove(racers[i]);
        }

        racers[i] = new RacingSquare(i,finished);
        add(racers[i],10,10 + (40*i));

        threads[i] = new Thread(racers[i]);
        threads[i].start();
      }
    }
  }

  private static final int NUM_RACERS = 14;
  private RacingSquare[] racers;
  private boolean[] finished;
  private Thread[] threads;

}

