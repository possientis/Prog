// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import java.awt.event.*; //

public class Event extends GraphicsProgram {

  public void init(){
    addMouseListeners();
  }

  // mouseClicked(e)
  // mousePressed(e) // pressed + released = clicked
  // mouseReleased(e)
  // mouseMoved(e)
  // mouseDragged(e)
  //
  public void mouseClicked(MouseEvent e){

    GLabel label = new GLabel("here",e.getX(),e.getY());
    add(label);
  }



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
