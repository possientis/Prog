// Rendering page elements sequentially
import java.util.*;

public class SingleThreadRenderer {
  void renderPage(CharSequence source) {
    renderText(source);
    List<ImageData> imageData = new ArrayList<ImageData>();
    for (ImageInfo imageInfo : scanForImageInfo(source))
      imageData.add(imageInfo.downloadImage());
    for (ImageData data : imageData)
      renderImage(data);
  }

  void renderText(CharSequence source){
  }

  void renderImage(ImageData data){
  }

  List<ImageInfo> scanForImageInfo(CharSequence source){
    return null;
  }
}


class ImageData {
}

class ImageInfo {
  public ImageData downloadImage(){
    return null;
  }
}
