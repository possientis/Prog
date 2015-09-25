// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import acm.util.*;  // RandomGenerator
import java.awt.*;  // Color
import java.awt.event.*; //

public class DragObject extends GraphicsProgram {

  public void init(){
    GRect rect = new GRect(100,100,150,100);
    rect.setFilled(true);
    add(rect);
    GOval oval = new GOval(50,50,150,100);
    oval.setFilled(true);
    add(oval);
    addMouseListeners();
    addKeyListeners();
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
  public void mouseDragged(MouseEvent e){

    if(gobj != null){
      gobj.move(e.getX()- last.getX(), e.getY() - last.getY());
      last = new GPoint(e.getPoint());
    }

  }

  public void mousePressed(MouseEvent e){

    last = new GPoint(e.getPoint());
    gobj = getElementAt(last);

  }

  public void keyTyped(KeyEvent e){

    if(gobj != null){
      gobj.setColor(rgen.nextColor());
    }
  }


  private GObject gobj;
  private GPoint last;
  private final RandomGenerator rgen = RandomGenerator.getInstance();



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
