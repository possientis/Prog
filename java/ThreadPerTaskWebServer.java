import java.io.*;
import java.net.*;

class ThreadPerTaskWebServer {
  public static void main(String[] args) throws IOException {
    ServerSocket socket = new ServerSocket(80);
    while (true) {
      final Socket connection = socket.accept();
      /*
      Runnable task = new Runnable() {
        public void run() {
          handleRequest(connection);
        }
      };
      */
      // modern lambda syntax
      Runnable task = () -> handleRequest(connection);
      new Thread(task).start();
    }
  }

  private static void handleRequest(Socket connection){
    // do something
    // The code must be thread-safe ...
  }
}
