import acm.graphics.*;
import acm.program.*;
import java.awt.*;
import acm.util.*;

public class RacingSquare extends GRect implements Runnable {

  public RacingSquare(int index, boolean[] finished){

    super(SIZE,SIZE);
    setFilled(true);
    myIndex = index;
    finishers = finished;

  }

  public void run(){

    finishers[myIndex] = false;

    for(int i = 0; i < 100; ++i)
    {
      pause(rgen.nextInt(50,65));
      move(STEP,0);
    }

    int count = 0;
    for(int i = 0; i < finishers.length; ++i){
      if(finishers[i]) count++;
    }

    // victory dance
    pause(50);

    finishers[myIndex] = true;

    if(count == 0){

      setColor(Color.RED);

    }

  }

  private int myIndex;
  private boolean[] finishers;
  private RandomGenerator rgen = RandomGenerator.getInstance();

  private static final int STEP = 5;
  private static final int SIZE = 20;

}
