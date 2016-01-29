// Web server with shutdown support
// ExecutorService interface is the key...
import java.util.concurrent.*;
import java.net.*;
import java.io.*;

class LifecycleWebServer {
  private final BlockingQueue<Runnable> workQueue = new LinkedBlockingQueue<>(); // should be somewhere else
  private final ExecutorService exec = new ThreadPoolExecutor(3,5,60,TimeUnit.SECONDS, workQueue); // some impl
  public void start() throws IOException {
    ServerSocket socket = new ServerSocket(80);
    while (!exec.isShutdown()) {
      try {
        final Socket conn = socket.accept();
        exec.execute(() -> handleRequest(conn));  // modern lambda syntax
        /*
        exec.execute(new Runnable() {
          public void run() { handleRequest(conn); }
        });
        */
      } catch (RejectedExecutionException e) {
        if (!exec.isShutdown())
          log("task submission rejected", e);
      }
    }
  }

  public void stop() { exec.shutdown(); }

  void handleRequest(Socket connection) {
    Request req = readRequest(connection);
    if (isShutdownRequest(req))
      stop();
    else
      dispatchRequest(req);
  }
  private void dispatchRequest(Request req){}

  private void log(String message, Exception e){}

  private Request readRequest(Socket connection){
    return new Request();
  }
  private boolean isShutdownRequest(Request req){
    return false;
  }

}

class Request{
}
