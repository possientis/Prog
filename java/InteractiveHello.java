import javax.swing.*;


public class InteractiveHello {

  public static void main(String[] args) {

    JFrame frame = new JFrame("Interactive Hello");
    frame.add(new MovingLabel("CS106A ricks!", 200, 200));
    frame.setSize(500,300);
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    frame.setVisible(true);

  }
}
