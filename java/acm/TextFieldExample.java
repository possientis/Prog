// Rename file Test.java
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import acm.util.*;
import java.awt.event.*;
import javax.swing.*;

public class TextFieldExample extends ConsoleProgram {

  public void init() {

    hiButton = new JButton("Hi");
    add(hiButton,SOUTH);


    tf = new JTextField(10);
    tf.addActionListener(this);
    add(new JLabel("Name:  "),SOUTH);
    add(tf,SOUTH);




    addActionListeners();
    }

  // do not misspell 'actionPerformed'....
  public void actionPerformed(ActionEvent e){

    //String cmd = e.getActionCommand();
    if(hiButton == e.getSource()){
      println("Hello there!");
    }

    if(tf == e.getSource()){
      println("Hi " + tf.getText());
    }
  }


  private JButton hiButton;
  private JTextField tf;


}

