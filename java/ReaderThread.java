// Encapsulating Nonstandard Cancellation in a Thread by Overriding Interrupt.
import java.io.*;
import java.net.*;

public class ReaderThread extends Thread {
  private final Socket socket;
  private final InputStream in;

  public ReaderThread(Socket socket) throws IOException {
    this.socket = socket;
    this.in = socket.getInputStream();  // may throw
  }

  @Override
  public void interrupt() {
    try {
      socket.close();
    }
    catch (IOException ignored) { }
    finally {
      super.interrupt();
    }
  }

  public void run() {
    try {
      byte[] buf = new byte[BUFSZ];
      while (true) {
        int count = in.read(buf);
        if (count < 0)
          break;
        else if (count > 0)
          processBuffer(buf, count);
      }
    } catch (IOException e) { /* Allow thread to exit */
    }
  }

  private final int BUFSZ = 1024;
  private void processBuffer(byte[] buf, int count){
  }

}
