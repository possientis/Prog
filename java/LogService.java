// Adding reliable cancellation to LogWriter
import java.util.concurrent.*;
import java.io.*;

public class LogService {
  private final BlockingQueue<String> queue;
  private final LoggerThread loggerThread;
  private final PrintWriter writer;
  // guarded by 'this'
  private boolean isShutdown;
  // guarded by this
  private int reservations;
  
  public LogService(PrintWriter writer){
    this.queue = new LinkedBlockingQueue<String>(512);
    this.loggerThread = new LoggerThread();
    this.writer = writer;
    this.isShutdown = false;
    this.reservations = 0;
  }

  public void start() { loggerThread.start(); }
  public void stop() {
    synchronized (this) { isShutdown = true; }
    loggerThread.interrupt();
  }

  public void log(String msg) throws InterruptedException {
    synchronized (this) {
      if (isShutdown)
        throw new IllegalStateException("Something");
      ++reservations;
    }
    queue.put(msg);
  }

  private class LoggerThread extends Thread {
    public void run() {
      try {
        while (true) {
          try {
            synchronized (this) {
              // this is the key: no shutdown until executing tasks have
              // all completed (reservations == 0)
              if (isShutdown && reservations == 0)
                break;
            }
            String msg = queue.take();
            synchronized (this) { --reservations; }
            writer.println(msg);
          } catch (InterruptedException e) { /* retry */ }
        }
      } finally {
        writer.close();
      }
    }
  }
}


