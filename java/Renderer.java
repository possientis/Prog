import java.util.*;
import java.util.concurrent.*;


public class Renderer {

  private final ExecutorService executor;

  Renderer(ExecutorService executor) { this.executor = executor; }

  void renderPage(CharSequence source) {

    final List<ImageInfo> info = scanForImageInfo(source);

    CompletionService<ImageData> completionService 
      = new ExecutorCompletionService<>(executor);

    for (final ImageInfo imageInfo : info)
      /*
      completionService.submit(new Callable<ImageData>() {
        public ImageData call() {
          return imageInfo.downloadImage();
        }
      });
      */
      completionService.submit(() -> {return imageInfo.downloadImage();});
    
    renderText(source);

    try {
      for (int t = 0, n = info.size(); t < n; t++) {
        Future<ImageData> f = completionService.take();
        ImageData imageData = f.get();
        renderImage(imageData);
      }
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
    } catch (ExecutionException e) {
      throw launderThrowable(e.getCause());
    }
  }

  Page renderPageWithAd() throws InterruptedException {
    long endNanos = System.nanoTime() + TIME_BUDGET;
    Future<Ad> f = executor.submit(new FetchAdTask());
    // Render the page while waiting for the ad
    Page page = renderPageBody();
    Ad ad;
    try {
      // Only wait for the remaining time budget
      long timeLeft = endNanos - System.nanoTime();
      ad = f.get(timeLeft, TimeUnit.NANOSECONDS);
    } catch (ExecutionException e) {
      ad = DEFAULT_AD;
    } catch (TimeoutException e) {
      ad = DEFAULT_AD;
      f.cancel(true);
    }
     page.setAd(ad);
    return page;
    }
  
  private final Ad DEFAULT_AD = null;
  private final long TIME_BUDGET = 0;

  private  List<ImageInfo> scanForImageInfo(CharSequence source){
    return null;
  }

  private void renderText(CharSequence source){
  }

  private void renderImage(ImageData imageData){
  }

  private Page renderPageBody(){
    return null;
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

class Page {
  public void setAd(Ad ad){
  }
}

class FetchAdTask implements Callable<Ad> {
  public Ad call(){
    return null;
  }
}

class Ad {
}

class ImageInfo {
  public ImageData downloadImage(){
    return null;
  }
}

class ImageData {
}
