import javax.swing.*;
import java.awt.event.*;
import java.awt.*;

public class MovingLabel extends JComponent implements MouseListener {

  public MovingLabel(String labelText, int startX, int startY) {
    text = labelText;
    x = startX;
    y = startY;
    addMouseListener(this);
  }


  public void paintComponent(Graphics g){
    g.drawString(text,x,y);
  }

  public void mouseClicked(MouseEvent e) {
    x = e.getX();
    y = e.getY();
    repaint();
  }

  public void mousePressed(MouseEvent e){}
  public void mouseReleased(MouseEvent e){}
  public void mouseEntered(MouseEvent e){}
  public void mouseExited(MouseEvent e){}



  private String text;
  private int x;
  private int y;

}
