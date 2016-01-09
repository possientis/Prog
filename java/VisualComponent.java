import java.util.*;
import java.util.concurrent.*;

public class VisualComponent {
  private final List<KeyListener> keyListeners 
    = new CopyOnWriteArrayList<KeyListener>();
  private final List<MouseListener> mouseListeners
    = new CopyOnWriteArrayList<MouseListener>();
  public void addKeyListener(KeyListener listener) {
    keyListeners.add(listener);
  }
  public void addMouseListener(MouseListener listener) {
    mouseListeners.add(listener);
  }
  public void removeKeyListener(KeyListener listener) {
    keyListeners.remove(listener);
  }
  public void removeMouseListener(MouseListener listener) {
    mouseListeners.remove(listener);
  }
}

class KeyListener {
}

class MouseListener {
}
