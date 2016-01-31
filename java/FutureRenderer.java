// Waiting for Image Download with Future
import java.util.*;
import java.util.concurrent.*;

class ImageInfo {
  public ImageData downloadImage(){
    return null;
  }
}

class ImageData {
}

public class FutureRenderer {
  // creating queue here for convenience
  private final BlockingQueue<Runnable> workQueue = new LinkedBlockingQueue<>();
  // instantiating something so this compiles at least
  private final ExecutorService executor 
    = new ThreadPoolExecutor(3,5,60,TimeUnit.SECONDS,workQueue);

  void renderPage(CharSequence source) {
    
    final List<ImageInfo> imageInfos = scanForImageInfo(source);

    Callable<List<ImageData>> task = new Callable<List<ImageData>>() {
        public List<ImageData> call() {
          List<ImageData> result = new ArrayList<ImageData>();
          for (ImageInfo imageInfo : imageInfos)
            result.add(imageInfo.downloadImage());
          return result;
        }
      };

    Future<List<ImageData>> future = executor.submit(task);
    renderText(source);
   
    try {
      List<ImageData> imageData = future.get();
      for (ImageData data : imageData)
        renderImage(data);
    } catch (InterruptedException e) {
        // Re-assert the thread's interrupted status
        Thread.currentThread().interrupt();
        // We don't need the result, so cancel the task too
        future.cancel(true);
    } catch (ExecutionException e) {
        throw launderThrowable(e.getCause());
    }
  }
  
  private List<ImageInfo> scanForImageInfo(CharSequence source){
    return null;
  }

  private void renderText(CharSequence source){
  }

  private void renderImage(ImageData data){
  }

  public static RuntimeException launderThrowable(Throwable t) {
    if (t instanceof RuntimeException)
      return (RuntimeException) t;
    else if (t instanceof Error)
      throw (Error) t;
    else
      throw new IllegalStateException("Not unchecked", t);
  }
}


