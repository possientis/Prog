// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import java.awt.event.*; //
import java.util.ArrayList;

public class MyArray extends GraphicsProgram {

  public void run(){

    addMouseListeners();
  }

  // keyPressed(e) e of type KeyEvent
  // keyReleased(e)
  // keyTyped(e) (pressed + release)
  // mouseClicked(e)
  // mousePressed(e) // pressed + released = clicked
  // mouseReleased(e)
  // mouseMoved(e)
  // mouseDragged(e)
  //
  public void mouseClicked(MouseEvent e){

    // Create a new label
    GLabel lab = new GLabel("#" + labels.size());
    lab.setFont("Courier-" + (10 + labels.size()));

    // Move all existing labels down one row
    double dy = lab.getHeight();
    for(int i = 0; i< labels.size(); ++i){
      labels.get(i).move(0,dy);
    }
    add(lab, START_X, START_Y);
    labels.add(lab);
  }

  private ArrayList<GLabel> labels = new ArrayList<GLabel>();
  private final int START_X = 50;
  private final int START_Y = 200;

}

/* GObject
 * object.setColor(color)
 * object.setLocation(x,y)
 * object.move(dx,dy)
 *
 * GLabel
 * new GLabel(text,x,y)
 * label.setFont(font) ("family-style-size")
 *
 * GRect
 * new GRect(x,y,width,height)
 *
 * GOvel
 * new GOval(x,y,width, height)
 *
 * GLine
 * new Gline(x0,y0,x1,y1)
 *
 * object.setFilled(boolean)  // GRect or GOval
 * object.setFillColor(color) //      "
 *
 * GraphicsProgram
 * object.getHeight()
 * object.getWidth()
 *
 */
