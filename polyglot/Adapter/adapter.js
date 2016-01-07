// Adapter design pattern

// This is the 'target' interface, namely the interface our Adapter
// will need to implement, relying on the 'adaptee' interface

function MediaPlayer(){
}
MediaPlayer.prototype.play = function(audioType, filename){
  print("MediaPlayer::play is not implemented");
}

// This is the 'adaptee' interface, of which concrete implementations
// provide the functionality allowing us to implement the adaptor

function AdvancedMediaPlayer(){
}
AdvancedMediaPlayer.prototype.playVlc = function(filename){
  print("AdvancedMediaPlayer::playVlc is not implemented");
}
AdvancedMediaPlayer.prototype.playMp4 = function(filename){
  print("AdvancedMediaPlayer::playMp4 is not implemented");
}

// one implementation of the adaptee interface
function VlcPlayer(){
  AdvancedMediaPlayer.call(this);
}
VlcPlayer.prototype = Object.create(AdvancedMediaPlayer.prototype);
// override
VlcPlayer.prototype.playVlc = function(filename){
  print("Playing vlc file. Name: " + filename);
}
// override
VlcPlayer.prototype.playMp4 = function(filename){
  // do nothing
}

// another implementation of the adaptee interface
function Mp4Player(){
  AdvancedMediaPlayer.call(this);
}
Mp4Player.prototype = Object.create(AdvancedMediaPlayer.prototype);
// override
Mp4Player.prototype.playVlc = function(filename){
  // do nothing
}
Mp4Player.prototype.playMp4 = function(filename){
  print("Playing mp4 file. Name: " + filename);
}

// Creating adapter class implementing the target interface
function MediaAdapter(audioType){
  MediaPlayer.call(this);
  if(audioType.toUpperCase() === "VLC"){
    this.advancedMusicPlayer = new VlcPlayer();
  } else if(audioType.toUpperCase() === "MP4"){
    this.advancedMusicPlayer = new Mp4Player();
  }
}
MediaAdapter.prototype = Object.create(MediaPlayer.prototype);
// override
MediaAdapter.prototype.play = function(audioType, filename){
  if(audioType.toUpperCase() === "VLC"){
    this.advancedMusicPlayer.playVlc(filename);
  } else if (audioType.toUpperCase() === "MP4"){
    this.advancedMusicPlayer.playMp4(filename);
  }
}

// Creating new class of MediaPlayer which uses our adaptor (optional)
function AudioPlayer(){
  MediaPlayer.call(this);
}
AudioPlayer.prototype = Object.create(MediaPlayer.prototype);
// override
AudioPlayer.prototype.play = function(audioType, filename){
  // in-built support for mp3 music file
  if(audioType.toUpperCase() === "MP3"){
    print("Playing mp3 file. Name: " + filename);
  }
  // mediaAdapter is providing support to play other file format
  else if(audioType.toUpperCase() === "VLC" || audioType.toUpperCase() === "MP4"){
    this.mediaAdapter = new MediaAdapter(audioType);
    this.mediaAdapter.play(audioType, filename);
  }
  else{
    print("Invalid media. " + audioType + " format not supported");
  }
}

// We can now use the AudioPlayer to play different types of audio formats
audioPlayer = new AudioPlayer();
audioPlayer.play("mp3", "beyond the horizon.mp3");
audioPlayer.play("mp4", "alone.mp4");
audioPlayer.play("vlc", "far far away.vlc");
audioPlayer.play("avi", "mind me.avi");
 


  




