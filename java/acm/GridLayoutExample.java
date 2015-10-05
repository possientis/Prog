// Rename file Test.java
import acm.gui.*;
import acm.graphics.*;
import acm.program.*;
import java.awt.*;  // Color
import acm.util.*;
import java.awt.event.*;
import javax.swing.*;

public class GridLayoutExample extends Program {

  public void init() {

    setLayout(new TableLayout(2,3));
//    setLayout(new GridLayout(2,3));

    add(new JButton("button 1"));
    add(new JButton("button 2"));
    add(new JButton("button 3"));
    add(new JButton("button 4"));
    add(new JButton("button 5"));
    add(new JButton("button 6"));

    addActionListeners();

  }

  // do not misspell 'actionPerformed'....
  public void actionPerformed(ActionEvent e){

  }


}

