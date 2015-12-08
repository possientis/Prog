// Adapter design pattern
using System;

// This the 'target' interface, namely the interface our Adapter
// will need to implement, relying on the 'adaptee' interface
interface MediaPlayer { 
  void play(string audioType, string filename);
}

// This is the 'adaptee' interface, of which concrete implementations
// provide the functionality allowing us to implement the adaptor
interface AdvancedMediaPlayer { // the adaptee
  void playVlc(string filename);
  void playMp4(string filename);
}

// one implementation of the adaptee interface
class VlcPlayer : AdvancedMediaPlayer {
  public void playVlc(string filename){
    Console.WriteLine("Playing vlc file. Name: " + filename);
  }
  public void playMp4(string filename){
    // do nothing
  }
}

// another implementation of the adaptee interface
class Mp4Player : AdvancedMediaPlayer {
  public void playVlc(string filename){
    // do nothing
  }
  public void playMp4(string filename){
    Console.WriteLine("Playing mp4 file. Name: " + filename);
  }
}

// Creating adapter class implementing the target interface
class MediaAdapter : MediaPlayer {
  // adapter implemented using composition (may use private inheritance in C++)
  private AdvancedMediaPlayer advancedMusicPlayer;
  // constructor
  public MediaAdapter(string audioType){
    if(audioType.Equals("vlc", StringComparison.OrdinalIgnoreCase)){
      advancedMusicPlayer = new VlcPlayer();
    } else if (audioType.Equals("mp4", StringComparison.OrdinalIgnoreCase)){
      advancedMusicPlayer = new Mp4Player();
    }
  }
  public void play(string audioType, string filename){
    if(audioType.Equals("vlc", StringComparison.OrdinalIgnoreCase)){
      advancedMusicPlayer.playVlc(filename);
    } else if (audioType.Equals("mp4", StringComparison.OrdinalIgnoreCase)){
      advancedMusicPlayer.playMp4(filename);
    }
  }
}

// Creating new class of MediaPlayer which uses our adaptor (optional)
class AudioPlayer : MediaPlayer {
  private MediaAdapter mediaAdapter;  // may be needed
  public void play(string audioType, string filename){
    // inbuilt support for mp3 music file
    if(audioType.Equals("mp3", StringComparison.OrdinalIgnoreCase)){
      Console.WriteLine("Playing mp3 file. Name: " + filename);
    }
    // mediaAdapter is providing support to play other file formats
    else if(audioType.Equals("vlc", StringComparison.OrdinalIgnoreCase) || 
            audioType.Equals("mp4", StringComparison.OrdinalIgnoreCase)){
      mediaAdapter = new MediaAdapter(audioType);
      mediaAdapter.play(audioType,filename);
    }
    else{
      Console.WriteLine("Invalid media. " + audioType + " format not supported");
    }
  }
}

// We can now use the AudioPlayer to play different types of audio formats
public class Adapter {
  public static void Main(string[] args){
    AudioPlayer audioPlayer = new AudioPlayer();
    audioPlayer.play("mp3", "beyond the horizon.mp3");
    audioPlayer.play("mp4", "alone.mp4");
    audioPlayer.play("vlc", "far far away.vlc");
    audioPlayer.play("avi", "mind me.avi");
  }
}
