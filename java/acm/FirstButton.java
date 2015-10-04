import acm.program.*;
import java.awt.event.*;
import javax.swing.*;

//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class FirstButton extends ConsoleProgram {


  public void init(){

    setFont("Courier-24");

    add(new JButton("Hi"), SOUTH);
    addActionListeners();

  }

  public void actionPerformed(ActionEvent e){


      String cmd = e.getActionCommand();
      if(cmd.equals("Hi")){
        println("Hello");
      }

  }

}
