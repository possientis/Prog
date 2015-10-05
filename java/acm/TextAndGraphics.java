// Rename file Test.java
import acm.gui.*;
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import acm.util.*;
import java.awt.event.*;
import javax.swing.*;

public class TextAndGraphics extends ConsoleProgram {

  public void init() {
    setLayout(new GridLayout(1,3));

    leftCanvas = new GCanvas();
    add(leftCanvas);  // goes to 2nd slot as console fills first

    rightCanvas = new GCanvas();
    add(rightCanvas);

    textField = new JTextField(10); // max size is 10
    add(new JLabel("Some text"), SOUTH);
    add(textField, SOUTH);
    textField.addActionListener(this);

    add(new JButton("Draw Left"), SOUTH);
    add(new JButton("Draw Right"), SOUTH);

    addActionListeners(); // required for buttons

  }

  // do not misspell 'actionPerformed'....
  public void actionPerformed(ActionEvent e){

    if(e.getSource() == textField){
      println("You typed " + textField.getText());
    }

    String cmd = e.getActionCommand();
    if(cmd.equals("Draw Left")){
      leftCanvas.add(createFilledRect(),20, leftY);
      leftY += SPACER;
    } else if(cmd.equals("Draw Right")){
      rightCanvas.add(createFilledRect(), 20, rightY);
      rightY += SPACER;
    }

  }

  private GRect createFilledRect(){
    GRect rect = new GRect(50,20);
    rect.setFilled(true);
    return rect;
  }

  private static final double SPACER = 30;

  private GCanvas leftCanvas;
  private GCanvas rightCanvas;
  private JTextField textField;

  private double leftY = 10;
  private double rightY = 10;


}

