// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import java.awt.event.*; //
import java.util.ArrayList;

public class GrayImage extends GraphicsProgram {

  public void run(){

    GImage image = new GImage("image.jpg");
    GImage grayImage = createGrayscaleImage(image);
    image.scale(1.25);
    add(image,10,0);
    grayImage.scale(1.25);
    add(grayImage,20 + image.getWidth(), 0);


  }

  private GImage createGrayscaleImage(GImage image){

    int[][] array = image.getPixelArray();

    int height = array.length;
    int width = array[0].length;

    for(int i = 0; i < height; ++i){
      for(int j = 0; j < width; ++j){
        int pixel = array[i][j];

        int r = GImage.getRed(pixel);
        int g = GImage.getGreen(pixel);
        int b = GImage.getBlue(pixel);

        int xx = computeLuminosity(r,g,b);
        array[i][j] = GImage.createRGBPixel(xx,xx,xx);
      }
    }

    return new GImage(array);
  }


  private int computeLuminosity(int r, int g, int b) {
      return GMath.round((0.299 * r) + (0.587 * g) + (0.114 * b));
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
