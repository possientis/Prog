// Adapter design pattern

// This the 'target' interface, namely the interface our Adapter
// will need to implement, relying on the 'adaptee' interface
abstract class MediaPlayer {
  def play(audioType: String, filename: String)
}

// This is the 'adaptee' interface, of which concrete implementations
// provide the functionality allowing us to implement the adaptor
abstract class AdvancedMediaPlayer {
  def playVlc(filename: String)
  def playMp4(filename: String)
}

// one implementation of the adaptee interface
class VlcPlayer extends AdvancedMediaPlayer {
  def playVlc(filename: String) = println("Playing vlc file. Name: " + filename)
  def playMp4(filename: String) = {/* do nothing */} 
}

// another implementation of the adaptee interface
class Mp4Player extends AdvancedMediaPlayer {
  def playMp4(filename: String) = println("Playing mp4 file. Name: " + filename)
  def playVlc(filename: String) = {/* do nothing */} 
}

// Creating adapter class implementing the target interface
class MediaAdapter(audioType: String) extends MediaPlayer {
  var advancedMusicPlayer: AdvancedMediaPlayer = null
  if(audioType.equalsIgnoreCase("vlc")){
    advancedMusicPlayer = new VlcPlayer
  } else if (audioType.equalsIgnoreCase("mp4")){
    advancedMusicPlayer = new Mp4Player
  }

  def play(audioType: String, filename: String) = {
    if(audioType.equalsIgnoreCase("vlc")){
      advancedMusicPlayer.playVlc(filename)
    } else if (audioType.equalsIgnoreCase("mp4")){
      advancedMusicPlayer.playMp4(filename)
    }
  }
}

// Creating new class of MediaPlayer which uses our adaptor (optional)
class AudioPlayer extends MediaPlayer {
  var mediaAdapter: MediaAdapter = null
  def play(audioType: String, filename: String) = {
    // in-built support for mp3 music files
    if(audioType.equalsIgnoreCase("mp3")){
      println("Playing mp3 file. Name: " + filename)
    } 
    // mediaAdapter is providing support to play other file formats
    else if(audioType.equalsIgnoreCase("vlc")||audioType.equalsIgnoreCase("mp4")){
      mediaAdapter = new MediaAdapter(audioType)
      mediaAdapter.play(audioType,filename)
    } else {
      println("Invalid media. %s format not supported" format audioType)
    }
  }
}



// We can now use the AudioPlayer to play different types of audio formats
object Adapter {
  def main(args: Array[String]){
    val audioPlayer = new AudioPlayer
    audioPlayer.play("mp3", "beyond the horizon.mp3");
    audioPlayer.play("mp4", "alone.mp4");
    audioPlayer.play("vlc", "far far away.vlc");
    audioPlayer.play("avi", "mind me.avi");
  }
}
