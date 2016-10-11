-- Adapter design pattern
import Data.Char  -- toUpper

type AudioType = String
type FileName = String

-- This the 'target' interface, namely the interface our Adapter
-- will need to implement, relying on the 'adaptee' interface
class MediaPlayer a where
  play :: a -> AudioType -> FileName -> IO ()
  play _ _ _ = putStrLn "MediaPlayer::play is not implemented"

-- This is the 'adaptee' interface, of which concrete implementations
-- provide the functionality allowing us to implement the adaptor
class IAdvancedMediaPlayer a where
  playVlc :: a -> FileName -> IO()
  playVlc _ _ = putStrLn "AdvancedMediaPlayer::playVlc is not implemented"
  playMp4 :: a -> FileName -> IO()
  playMp4 _ _ = putStrLn "AdvancedMediaPlayer::playMp4 is not implemented"

-- one implementation of the adaptee interface
data VlcPlayer = VlcPlayer
instance IAdvancedMediaPlayer VlcPlayer where
  playVlc VlcPlayer filename  = putStrLn ("Playing vlc file. Name: " ++ filename)
  playMp4 VlcPlayer _         = return () -- do nothing 

-- another implementation of the adaptee interface
data Mp4Player = Mp4Player
instance IAdvancedMediaPlayer Mp4Player where
  playVlc Mp4Player _         = return ()
  playMp4 Mp4Player filename  = putStrLn ("Playing mp4 file. Name: " ++ filename)

data AdvancedMediaPlayer = MkVlc VlcPlayer | MkMp4 Mp4Player
instance IAdvancedMediaPlayer AdvancedMediaPlayer where
  playVlc (MkVlc x) = playVlc x
  playVlc (MkMp4 x) = playVlc x
  playMp4 (MkVlc x) = playMp4 x
  playMp4 (MkMp4 x) = playMp4 x

-- Creating adapter class implementing the target interface
data MediaAdapter = MediaAdapter AudioType
advancedMusicPlayer :: MediaAdapter -> AdvancedMediaPlayer
advancedMusicPlayer (MediaAdapter audioType) =
  case map toUpper audioType of
    "VLC"   -> MkVlc VlcPlayer
    "MP4"   -> MkMp4 Mp4Player
    otherwise -> error "advancedMusicPlayer: invalid audioType"

instance MediaPlayer MediaAdapter where
  play adapter audioType filename = case map toUpper audioType of
    "VLC" -> playVlc musicPlayer filename
    "MP4" -> playMp4 musicPlayer filename
    otherwise -> error "MediaAdapter::play: invalid audioType"
    where
      musicPlayer = advancedMusicPlayer adapter

-- Creating new class of MediaPlayer which uses our adaptor (optional)
data AudioPlayer = AudioPlayer
instance MediaPlayer AudioPlayer where
  play player audioType filename = let upper = map toUpper audioType in
    -- in-built support for mp3 music file
    if upper == "MP3" then 
      putStrLn ("Playing mp3 file. Name: " ++ filename)   
    else if (upper ==  "VLC") || (upper == "MP4") then
      let adapter = MediaAdapter audioType
        in play adapter audioType filename 
    else
      putStrLn ("Invalid media. " ++ audioType ++ " format not supported")

-- We can now use the AudioPlayer to play different types of audio formats
main = let audioPlayer = AudioPlayer in do
  play audioPlayer "mp3" "beyond the horizon.mp3"
  play audioPlayer "mp4" "alone.mp4"
  play audioPlayer "vlc" "far far away.vlc"
  play audioPlayer "avi" "mind me.avi"


