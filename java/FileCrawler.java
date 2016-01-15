import java.util.concurrent.*;
import java.io.*;

public class FileCrawler implements Runnable {
  private final BlockingQueue<File> fileQueue;
  private final FileFilter fileFilter;
  private final File root;

  public void run() {
    try {
        crawl(root);
    } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
    }
  }
  
  private void crawl(File root) throws InterruptedException {
    File[] entries = root.listFiles(fileFilter);
    if (entries != null) {
      for (File entry : entries)
        if (entry.isDirectory())
          crawl(entry);
        else if (!alreadyIndexed(entry))
          fileQueue.put(entry);
    }
  }

  // TBI
  private boolean alreadyIndexed(File entry){
    return false;
  }

  public FileCrawler(BlockingQueue<File> queue){
    fileQueue = queue;
    fileFilter = (File pathname) -> true;  // should be changed
    root = new File("/");                  // should be changed
  }
}

class Indexer implements Runnable {
  private final BlockingQueue<File> queue;
  public Indexer(BlockingQueue<File> queue) {
    this.queue = queue;
  }
  public void run() {
    try {
      while (true)                        // never terminates, should be changed
        indexFile(queue.take());
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }
  
  private void indexFile(File entry){
    System.out.println(entry.getName());
  }
}
