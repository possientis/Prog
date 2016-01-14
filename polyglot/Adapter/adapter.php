<?php
// Adapter design pattern

// This the 'target' interface, namely the interface our Adapter
// will need to implement, relying on the 'adaptee' interface
interface MediaPlayer {
  public function play($audioType, $filename);
}

// This is the 'adaptee' interface, of which concrete implementations
// provide the functionality allowing us to implement the adaptor
interface AdvancedMediaPlayer {
  public function playVlc($filename);
  public function playMp4($filename);
}

// one implementation of the adaptee interface
class VlcPlayer implements AdvancedMediaPlayer {
  public function playVlc($filename){
    echo "Playing vlc file. Name: $filename\n";
  }
  public function playMp4($filename){
    // do nothing
  }
}

// another implementation of the adaptee interface
class Mp4Player implements AdvancedMediaPlayer {
  public function playMp4($filename){
    echo "Playing mp4 file. Name: $filename\n";
  }
  public function playVlc($filename){
    // do nothing
  }
}

// Creating adapter class implementing the target interface
class MediaAdapter implements MediaPlayer {
  // adapter implemented using composition (may use private inheritance in C++)
  private $advancedMusicPlayer;
  // constructor
  public function __construct($audioType){
    if(strtoupper($audioType) == "VLC"){
      $this->advancedMusicPlayer = new VlcPlayer;
    } else if (strtoupper($audioType) == "MP4"){
      $this->advancedMusicPlayer = new Mp4Player;
    }
  }
  public function play($audioType, $filename){
    if(strtoupper($audioType) == "VLC"){
      $this->advancedMusicPlayer->playVlc($filename);
    } else if (strtoupper($audioType) == "MP4"){
      $this->advancedMusicPlayer->playMp4($filename);
    }
  }
}

// Creating new class of MediaPlayer which uses our adaptor (optional)
class AudioPlayer implements MediaPlayer {
  private $mediaAdapter;

  public function play($audioType,$filename){
    // in-built support for mp3 music file
    if(strtoupper($audioType) == "MP3"){
      echo "Playing mp3 file. Name: $filename\n";
    }
    // mediaAdapter is providing support to play other file formats
    else if (strtoupper($audioType) == "VLC" || strtoupper($audioType) == "MP4"){
      $this->mediaAdapter = new MediaAdapter($audioType);
      $this->mediaAdapter->play($audioType,$filename);
    }
    else {
      echo "Invalid media. $audioType format not supported\n";
    }
  }
}

// We can now use the AudioPlayer to play different types of audio formats
$audioPlayer = new AudioPlayer();
$audioPlayer->play("mp3", "beyond the horizon.mp3");
$audioPlayer->play("mp4", "alone.mp4");
$audioPlayer->play("vlc", "far far away.vlc");
$audioPlayer->play("avi", "mind me.avi");




?>
