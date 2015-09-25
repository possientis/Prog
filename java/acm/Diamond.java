// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color

public class Diamond extends GraphicsProgram {
  public void run() {
    GPolygon diamond = createDiamond(100,75);
    diamond.setFilled(true);
    diamond.setFillColor(Color.MAGENTA);
    add(diamond,getWidth()/2,getHeight()/2);
  }

  private GPolygon createDiamond(double width, double height){

    GPolygon diamond = new GPolygon();
    diamond.addVertex(-width/2,0);
    diamond.addVertex(0,-height/2);
    diamond.addVertex(width/2,0);
    diamond.addVertex(0,height/2);
    return diamond;
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
