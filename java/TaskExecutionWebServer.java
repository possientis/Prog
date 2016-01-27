import java.io.*;
import java.net.*;
import java.util.concurrent.*;

class TaskExecutionWebServer {
  private static final int NTHREADS = 100;
  private static final Executor exec = Executors.newFixedThreadPool(NTHREADS);
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
      Runnable task = () -> handleRequest(connection);
      exec.execute(task);
    }
  }
  private static void handleRequest(Socket connection){
    // do something
  }
}
