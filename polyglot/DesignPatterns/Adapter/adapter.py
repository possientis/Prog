# Adapter design pattern

# This the 'target' interface, namely the interface our Adapter
# will need to implement, relying on the 'adaptee' interface
class MediaPlayer:
    def play(self, audioType, filename):
        raise Exception("MediaPlayer::play is not implemented")

# This is the 'adaptee' interface, of which concrete implementations
# provide the functionality allowing us to implement the adaptor
class AdvancedMediaPlayer:
    def playVlc(self, filename):
        raise Exception("AdvancedMediaPlayer::playVlc is not implemented")
    def playMp4(self, filename):
        raise Exception("AdvancedMediaPlayer::playMp4 is not implemented")

# one implementation of the adaptee interface
class VlcPlayer(AdvancedMediaPlayer):
    def playVlc(self, filename):
        print("Playing vlc file. Name: " + filename)
    
    def playMp4(self, filename):
        pass # do nothing

# another implementation of the adaptee interface
class Mp4Player(AdvancedMediaPlayer):
    def playVlc(self, filename):
        pass # do nothing
    
    def playMp4(self, filename):
        print("Playing mp4 file. Name: " + filename)

# Creating adapter class implementing the target interface
class MediaAdapter(MediaPlayer):
    # adapter implemented using composition (may use private inheritance in C++)
    # constructor
    def __init__(self, audioType):
        if audioType.upper() == "VLC":
            self.advancedMusicPlayer = VlcPlayer()
        elif audioType.upper() == "MP4":
            self.advancedMusicPlayer = Mp4Player()
  
    def play(self, audioType, filename):
        if audioType.upper() == "VLC":
            self.advancedMusicPlayer.playVlc(filename)
        elif audioType.upper() == "MP4":
            self.advancedMusicPlayer.playMp4(filename)

# Creating new class of MediaPlayer which uses our adaptor (optional)
class AudioPlayer(MediaPlayer):
    def play(self,  audioType, filename):
        # inbuilt support for mp3 music file
        if audioType.upper() == "MP3":
            print("Playing mp3 file. Name: " + filename)
        # mediaAdapter is providing support to play other file formats
        elif audioType.upper() == "VLC" or  audioType.upper() == "MP4":
            self.mediaAdapter = MediaAdapter(audioType)
            self.mediaAdapter.play(audioType,filename)
        else:
            print("Invalid media. " + audioType + " format not supported")
            

# We can now use the AudioPlayer to play different types of audio formats
audioPlayer = AudioPlayer()
audioPlayer.play("mp3", "beyond the horizon.mp3")
audioPlayer.play("mp4", "alone.mp4")
audioPlayer.play("vlc", "far far away.vlc")
audioPlayer.play("avi", "imind me.avi")



