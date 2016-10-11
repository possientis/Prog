// Adapter design pattern
#include <iostream>
#include <string>
#include <boost/algorithm/string/predicate.hpp> // boost::iequals
#include <memory>
#include <assert.h>

// This the 'target' interface, namely the interface our Adapter
// will need to implement, relying on the 'adaptee' interface
class MediaPlayer { 
  public:
    virtual ~MediaPlayer(){}
    virtual void play(std::string audioType, std::string filename) const = 0;
};

// This is the 'adaptee' interface, of which concrete implementations
// provide the functionality allowing us to implement the adaptor
class AdvancedMediaPlayer {
  public:
    virtual ~AdvancedMediaPlayer(){}
    virtual void playVlc(std::string filename) const = 0;
    virtual void playMp4(std::string filename) const = 0;
};

// one implementation of the adaptee interface
class VlcPlayer : public AdvancedMediaPlayer {
  public:
    void playVlc(std::string filename) const override {
      std::cout << "Playing vlc file. Name: " << filename << std::endl;
    }
    void playMp4(std::string filename) const override {
    // do nothing
    }
};

// another implementation of the adaptee interface
class Mp4Player : public  AdvancedMediaPlayer {
  public:
    void playVlc(std::string filename) const override {
    // do nothing
    }
    void playMp4(std::string filename) const override {
      std::cout << "Playing mp4 file. Name: " << filename << std::endl;
    }
};

// Creating adapter class implementing the target interface
typedef std::shared_ptr<AdvancedMediaPlayer> AdvancedMediaPlayerPtr;
class MediaAdapter : public MediaPlayer {
  public:
  // constructor
    MediaAdapter(std::string audioType){
      if(boost::iequals(audioType,"vlc")){
        advancedMusicPlayer = AdvancedMediaPlayerPtr(new VlcPlayer());
      } else if (boost::iequals(audioType, "mp4")){
        advancedMusicPlayer = AdvancedMediaPlayerPtr(new Mp4Player());
      }
    }
    void play(std::string audioType, std::string filename) const override {
      if(boost::iequals(audioType, "vlc")){
        assert(advancedMusicPlayer != nullptr);
        advancedMusicPlayer->playVlc(filename);
      } else if (boost::iequals(audioType, "mp4")){
        assert(advancedMusicPlayer != nullptr);
        advancedMusicPlayer->playMp4(filename);
      }
    }
  private:
    AdvancedMediaPlayerPtr advancedMusicPlayer;
};

// Creating new class of MediaPlayer which uses our adaptor (optional)
typedef std::shared_ptr<MediaAdapter> MediaAdapterPtr;
class AudioPlayer : public MediaPlayer {
  public:
    void play(std::string audioType, std::string filename) const override {
      // inbuilt support for mp3 music file
      if(boost::iequals(audioType, "mp3")){
        std::cout << "Playing mp3 file. Name: " << filename << std::endl;
      }
      // mediaAdapter is providing support to play other file formats
      else if(boost::iequals(audioType, "vlc") || boost::iequals(audioType, "mp4")){
        mediaAdapter = MediaAdapterPtr(new MediaAdapter(audioType));
        assert(mediaAdapter != nullptr);
        mediaAdapter->play(audioType,filename);
      }
      else{
        std::cout << "Invalid media. " << audioType << " format not supported\n";
      }
    }

  private:
    // 'play' method declared const, but some internals may still be changed
    mutable MediaAdapterPtr mediaAdapter;  // may be needed
};


int main(int argc, char* argv[], char* envp[]){

  AudioPlayer audioPlayer;
  audioPlayer.play("mp3", "beyond the horizon.mp3");
  audioPlayer.play("mp4", "alone.mp4");
  audioPlayer.play("vlc", "far far away.vlc");
  audioPlayer.play("avi", "mind me.avi");

  return 0;
}
