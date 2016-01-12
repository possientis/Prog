# Adapter design pattern

# This the 'target' interface, namely the interface our Adapter
# will need to implement, relying on the 'adaptee' interface
class MediaPlayer
  def play(audioType,filename)
    raise Exception.new "MediaPlayer::play is not implemented"
  end
end

# This is the 'adaptee' interface, of which concrete implementations
# provide the functionality allowing us to implement the adaptor
class AdvancedMediaPlayer
  def playVlc(filename)
    raise Exception.new "AdvancedMediaPlayer::playVlc is not implemented"
  end
  def playMp4(filename)
    raise Exception.new "AdvancedMediaPlayer::playMp4 is not implemented"
  end
end

# one implementation of the adaptee interface
class VlcPlayer < AdvancedMediaPlayer
  def playVlc(filename)
    puts "Playing vlc file. Name: #{filename}"
  end
  def playMp4(filename)
    # do nothing
  end
end

# another implementation of the adaptee interface
class Mp4Player < AdvancedMediaPlayer
  def playMp4(filename)
    puts "Playing mp4 file. Name: #{filename}"
  end
  def playVlc(filename)
    # do nothing
  end
end

# Creating adapter class implementing the target interface
class MediaAdapter < MediaPlayer
  # adapter implemented using composition (may use private inheritance in C++)
  def initialize(audioType)
    if audioType.casecmp("vlc") == 0
      @advancedMusicPlayer = VlcPlayer.new
    elsif audioType.casecmp("mp4") == 0
      @advancedMusicPlayer = Mp4Player.new
    end
  end
  def play(audioType,filename)
    if audioType.casecmp("vlc") == 0
      @advancedMusicPlayer.playVlc filename
    elsif audioType.casecmp("mp4")
      @advancedMusicPlayer.playMp4 filename
    end
  end
end

# Creating new class of MediaPlayer which uses our adaptor (optional)
class AudioPlayer < MediaPlayer
  def play(audioType,filename)
    #in-built support for mp3 music file
    if audioType.casecmp("mp3") == 0
      puts "Playing mp3 file. Name: #{filename}"
    elsif audioType.casecmp("vlc") == 0 || audioType.casecmp("mp4") == 0
      @mediaAdapter = MediaAdapter.new(audioType)
      @mediaAdapter.play audioType, filename
    else
      puts "Invalid media. #{audioType} format not supported"
    end
  end
end

# We can now use the AudioPlayer to play different types of audio formats
audioPlayer = AudioPlayer.new
audioPlayer.play "mp3", "beyond the horizon.mp3"
audioPlayer.play "mp4", "alone.mp4"
audioPlayer.play "vlc", "far far away.vlc"
audioPlayer.play "avi", "mind me.avi"



