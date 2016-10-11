// Adapter design pattern


// This the 'target' interface, namely the interface our Adapter
// will need to implement, relying on the 'adaptee' interface
interface MediaPlayer { 
  void play(String audioType, String filename);
}

// This is the 'adaptee' interface, of which concrete implementations
// provide the functionality allowing us to implement the adaptor
interface AdvancedMediaPlayer {
  void playVlc(String filename);
  void playMp4(String filename);
}

// one implementation of the adaptee interface
class VlcPlayer implements AdvancedMediaPlayer {
  @Override
  public void playVlc(String filename){
    System.out.println("Playing vlc file. Name: " + filename);
  }
  @Override
  public void playMp4(String filename){
    // do nothing
  }
}

// another implementation of the adaptee interface
class Mp4Player implements AdvancedMediaPlayer {
  @Override
  public void playVlc(String filename){
    // do nothing
  }
  @Override
  public void playMp4(String filename){
    System.out.println("Playing mp4 file. Name: " + filename);
  }
}

// Creating adapter class implementing the target interface
class MediaAdapter implements MediaPlayer {
  // adapter implemented using composition (may use private inheritance in C++)
  private AdvancedMediaPlayer advancedMusicPlayer;
  // constructor
  public MediaAdapter(String audioType){
    if(audioType.equalsIgnoreCase("vlc")){
      advancedMusicPlayer = new VlcPlayer();
    } else if (audioType.equalsIgnoreCase("mp4")){
      advancedMusicPlayer = new Mp4Player();
    }
  }
  @Override
  public void play(String audioType, String filename){
    if(audioType.equalsIgnoreCase("vlc")){
      advancedMusicPlayer.playVlc(filename);
    } else if (audioType.equalsIgnoreCase("mp4")){
      advancedMusicPlayer.playMp4(filename);
    }
  }
}

// Creating new class of MediaPlayer which uses our adaptor (optional)
class AudioPlayer implements MediaPlayer {
  private MediaAdapter mediaAdapter;  // may be needed
  @Override
  public void play(String audioType, String filename){
    // inbuilt support for mp3 music file
    if(audioType.equalsIgnoreCase("mp3")){
      System.out.println("Playing mp3 file. Name: " + filename);
    }
    // mediaAdapter is providing support to play other file formats
    else if(audioType.equalsIgnoreCase("vlc") || audioType.equalsIgnoreCase("mp4")){
      mediaAdapter = new MediaAdapter(audioType);
      mediaAdapter.play(audioType,filename);
    }
    else{
      System.out.println("Invalid media. " + audioType + " format not supported");
    }
  }
}

// We can now use the AudioPlayer to play different types of audio formats
public class Adapter {
  public static void main(String[] args){
    AudioPlayer audioPlayer = new AudioPlayer();
    audioPlayer.play("mp3", "beyond the horizon.mp3");
    audioPlayer.play("mp4", "alone.mp4");
    audioPlayer.play("vlc", "far far away.vlc");
    audioPlayer.play("avi", "mind me.avi");
  }
}
