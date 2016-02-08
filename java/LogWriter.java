// producer consumer logging service with no shutdown support
import java.util.concurrent.*;
import java.io.*;

public class LogWriter {
  private final BlockingQueue<String> queue;
  private final LoggerThread logger;
  private final int CAPACITY = 512;

  public LogWriter(PrintWriter writer) {
    this.queue = new LinkedBlockingQueue<String>(CAPACITY);
    this.logger = new LoggerThread(writer);
  }

  public void start() { logger.start(); }

  public void log(String msg) throws InterruptedException {
    queue.put(msg);
  }

  private class LoggerThread extends Thread {
    private final PrintWriter writer;
    public LoggerThread(PrintWriter writer){
      this.writer = writer;
    }
    public void run() {
        try {
          while (true)
            writer.println(queue.take());
        } catch(InterruptedException ignored) {
        } finally {
          writer.close();
        }
    }
  }
}
