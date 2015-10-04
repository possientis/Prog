import acm.program.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class ButtonPress extends ConsoleProgram {


  public void init(){

    setFont("Courier-24");

    add(new JButton("Hello"), NORTH);
    add(new JButton("CS106A"), SOUTH);
    add(new JButton("BasketHeawing101"), SOUTH);
    addActionListeners();

  }

  public void actionPerformed(ActionEvent e){


      String cmd = e.getActionCommand();
      if(cmd.equals("Hello")){
        println("Hello there");
      } else if (cmd.equals("CS106A")){
        println("CS106A there");
      } else if (cmd.equals("BasketHeawing101")){
        println("Basket there");
      }

  }

}
