// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import java.awt.event.*; //necessary despite java.awt.*
import javax.swing.*;

public class InteractiveDrawFace extends GraphicsProgram {
  public void init() {
    // button to clear display
    add(new JButton("Clear"),SOUTH);

    // check box to display  front or back of face
    checkBox = new JCheckBox("Front");
    checkBox.setSelected(true);
    add(checkBox,SOUTH);

    initRadioButtons();
    initColorChooser();

    // must call this method to be able to get mouse events
    addMouseListeners();


    // must call this method to get button press events
    addActionListeners();

  }

  private void initRadioButtons(){
    ButtonGroup sizeBG = new ButtonGroup();

    smallRB = new JRadioButton("Small");
    medRB = new JRadioButton("Medium");
    largeRB = new JRadioButton("Large");

    sizeBG.add(smallRB);
    sizeBG.add(medRB);
    sizeBG.add(largeRB);

    medRB.setSelected(true);

    add(smallRB, SOUTH);
    add(medRB, SOUTH);
    add(largeRB, SOUTH);

  }

  private void initColorChooser(){
    pickColor = new JComboBox<String>();
    pickColor.addItem("Black");
    pickColor.addItem("Blue");
    pickColor.addItem("Green");
    pickColor.addItem("Red");

    // use cannot add colors
    pickColor.setEditable(false);

    pickColor.setSelectedItem("Black");

    add(new JLabel("   Color:"),SOUTH);

    add(pickColor, SOUTH);

  }

  public void mouseClicked(MouseEvent e){
    GObject obj;
    double diam = getDiamSize();
    if(checkBox.isSelected()){
      obj = new GOval(diam,diam); // get a GFace later
    }else{
      obj = new GOval(diam,diam);
    }

    obj.setColor(getCurrentColor());

    add(obj,e.getX(),e.getY());
  }

  private double getDiamSize(){
    double size = 0;

    if(smallRB.isSelected()){
      size = SMALL_DIAM;
    } else if (medRB.isSelected()){
      size = MED_DIAM;
    } else if (largeRB.isSelected()) {
      size = LARGE_DIAM;
    }

    return size;
  }

  private Color getCurrentColor(){

    String name = (String) pickColor.getSelectedItem();

    if(name.equals("Blue")){
      return Color.BLUE;
    } else if (name.equals("Green")){
      return Color.GREEN;
    } else if (name.equals("Red")){
      return Color.RED;
    } else return Color.BLACK;
  }

  public void actionPerformed(ActionEvent e){
    if(e.getActionCommand().equals("Clear")){
      removeAll();  // clears the canvas
    }
  }
  // private  constants
  private static final double SMALL_DIAM = 20;
  private static final double MED_DIAM = 40;
  private static final double LARGE_DIAM = 60;

  // data members
  private JCheckBox checkBox;
  private JRadioButton smallRB;
  private JRadioButton medRB;
  private JRadioButton largeRB;
  private JComboBox<String> pickColor;


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
