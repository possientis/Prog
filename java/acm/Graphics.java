// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color

public class Test extends GraphicsProgram {
  public void run() {
    GLabel label = new GLabel( "hello, world!!!!!", 100, 75);
    label.setFont("SansSerif-Bold-36");
    label.setColor(Color.RED);
    add(label);

    GRect rect1 = new GRect(10,10,50,50);
    add(rect1);

    GRect rect2 = new GRect(300,75,200,100);
    rect2.setFilled(true);
    rect2.setColor(Color.RED);
    add(rect2);

    GOval oval = new GOval(300,75,200,100);
    oval.setFilled(true);
    oval.setFillColor(Color.GREEN);
    add(oval);

    GLine myFunkyLine = new GLine(100,150,200,175);
    add(myFunkyLine);

    GLine line2 = new GLine(0,0,300,300);
    add(line2);
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
