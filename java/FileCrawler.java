import java.util.concurrent.*;
import java.io.*;

public class FileCrawler implements Runnable {
  private final BlockingQueue<File> fileQueue;
  private final FileFilter fileFilter;
  private final File root;
  public static void main(String[] args) throws InterruptedException {
    BlockingQueue<File> queue = new LinkedBlockingQueue<>();
    FileCrawler crawler = new FileCrawler(queue);
    Indexer indexer = new Indexer(queue);
    Thread t1 = new Thread(crawler);
    Thread t2 = new Thread(indexer);
    t1.start();
    t2.start();
  }

  public void run() {
    try {
        crawl(root);
    } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
    }
  }
  
  private void crawl(File root) throws InterruptedException {
//    System.out.println("Inside FileCrawler::crawl");
    System.out.println("FileCrawler entering directory " + root.getName());
    File[] entries = root.listFiles(fileFilter);
    if (entries != null) {
      for (File entry : entries)
        if (entry.isDirectory()){

          crawl(entry);
        }
        else if (!alreadyIndexed(entry))
          fileQueue.put(entry);
    }
    System.out.println("FileCrawler::crawl has completed directory " + root.getName());
  }

  // TBI
  private boolean alreadyIndexed(File entry){
    return false;
  }

  public FileCrawler(BlockingQueue<File> queue){
    fileQueue = queue;
    fileFilter = (File pathname) -> true;           // should be changed
    root = new File("/home/john");                  // should be changed
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
    //System.out.println(entry.getName());
  }
}
