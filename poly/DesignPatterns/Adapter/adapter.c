// Adapter design pattern
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <malloc.h>

// This the 'target' interface, namely the interface our Adapter
// will need to implement, relying on the 'adaptee' interface

typedef struct MediaPlayer_ MediaPlayer;
struct MediaPlayer_ {

};

void MediaPlayer_init(MediaPlayer* self){
}

void MediaPlayer_destroy(MediaPlayer* self){
}

typedef struct AdvancedMediaPlayer_ AdvancedMediaPlayer;
struct AdvancedMediaPlayer_ {
  void (*delete)(AdvancedMediaPlayer*); // virtual destruction of pointer
  void (*playVlc)(AdvancedMediaPlayer*, const char*); // virtual
  void (*playMp4)(AdvancedMediaPlayer*, const char*); // virtual
};

void AdvancedMediaPlayer_init(
    AdvancedMediaPlayer* self,
    void (*delete)(AdvancedMediaPlayer*),
    void (*playVlc)(AdvancedMediaPlayer*, const char*),
    void (*playMp4)(AdvancedMediaPlayer*, const char*)
    ){
  assert(self != NULL);
  self->delete = delete;
  self->playVlc = playVlc;
  self->playMp4 = playMp4;
}

void AdvancedMediaPlayer_destroy(AdvancedMediaPlayer* self){
  assert(self != NULL);
  self->delete = NULL;
}
// virtual
void AdvancedMediaPlayer_delete(AdvancedMediaPlayer* ptr){
  assert(ptr != NULL);
  void (*delete)(AdvancedMediaPlayer*);
  delete = ptr->delete;
  assert(delete != NULL);
  delete(ptr);
}

void AdvancedMediaPlayer_playVlc(AdvancedMediaPlayer* self, const char* filename){
  assert(self != NULL);
  assert(self->playVlc != NULL);
  self->playVlc(self, filename);
}

void AdvancedMediaPlayer_playMp4(AdvancedMediaPlayer* self, const char* filename){
  assert(self != NULL);
  assert(self->playMp4 != NULL);
  self->playMp4(self, filename);
}


typedef struct VlcPlayer_ VlcPlayer;
struct VlcPlayer_ {
  AdvancedMediaPlayer base;
};

void VlcPlayer_delete(AdvancedMediaPlayer*);  // override needed for init
void VlcPlayer_playVlc(AdvancedMediaPlayer*, const char*);
void VlcPlayer_playMp4(AdvancedMediaPlayer*, const char*);
void VlcPlayer_init(VlcPlayer* self){
  assert(self != NULL);
  AdvancedMediaPlayer_init(
      &self->base, 
      VlcPlayer_delete, 
      VlcPlayer_playVlc, 
      VlcPlayer_playMp4
  );
}

VlcPlayer *VlcPlayer_new(){
  VlcPlayer* obj = (VlcPlayer*) malloc(sizeof(VlcPlayer));
  VlcPlayer_init(obj);
  assert(obj != NULL);
  return obj;
}

void VlcPlayer_destroy(VlcPlayer *self){
  assert(self != NULL);
  AdvancedMediaPlayer_destroy(&self->base);
}

// override
void VlcPlayer_delete(AdvancedMediaPlayer* ptr){
  assert(ptr != NULL);
  VlcPlayer* obj = (VlcPlayer*) ptr;
  VlcPlayer_destroy(obj);
  free(obj);
}

// override
void VlcPlayer_playVlc(AdvancedMediaPlayer* self, const char* filename){
  printf("Playing vlc file. Name: %s\n", filename);
}

// override
void VlcPlayer_playMp4(AdvancedMediaPlayer* self, const char* filename){
  // do nothing
} 

typedef struct Mp4Player_ Mp4Player;
struct Mp4Player_ {
    AdvancedMediaPlayer base;
};

void Mp4Player_delete(AdvancedMediaPlayer*);  // override needed for init
void Mp4Player_playVlc(AdvancedMediaPlayer*, const char*);
void Mp4Player_playMp4(AdvancedMediaPlayer*, const char*);
void Mp4Player_init(Mp4Player* self){
  assert(self != NULL);
  AdvancedMediaPlayer_init(
      &self->base, 
      Mp4Player_delete,
      Mp4Player_playVlc,
      Mp4Player_playMp4
  );
}

Mp4Player *Mp4Player_new(){
  Mp4Player* obj = (Mp4Player*) malloc(sizeof(Mp4Player));
  Mp4Player_init(obj);
  assert(obj != NULL);
  return obj;
}

void Mp4Player_destroy(Mp4Player *self){
  assert(self != NULL);
  AdvancedMediaPlayer_destroy(&self->base);
}

// override
void Mp4Player_delete(AdvancedMediaPlayer* ptr){
  assert(ptr != NULL);
  Mp4Player* obj = (Mp4Player*) ptr;
  Mp4Player_destroy(obj);
  free(obj);
}

// override
void Mp4Player_playMp4(AdvancedMediaPlayer* self, const char* filename){
  printf("Playing mp4 file. Name: %s\n", filename);
}

// override
void Mp4Player_playVlc(AdvancedMediaPlayer* self, const char* filename){
  // do nothing
} 


typedef struct MediaAdapter_ MediaAdapter;
struct MediaAdapter_ {
  MediaPlayer base;
  AdvancedMediaPlayer *advancedMusicPlayer;
};

void MediaAdapter_init(MediaAdapter* self, const char* audioType){
  assert(self != NULL);
  MediaPlayer_init(&self->base);
  if(strcasecmp(audioType, "VLC") == 0){
    self->advancedMusicPlayer = &VlcPlayer_new()->base;
  } else if (strcasecmp(audioType, "MP4") == 0){
    self->advancedMusicPlayer = &Mp4Player_new()->base;
  }
}

void MediaAdapter_destroy(MediaAdapter* self){
  assert(self != NULL);
  MediaPlayer_destroy(&self->base);
  AdvancedMediaPlayer_delete(self->advancedMusicPlayer);
  self->advancedMusicPlayer = NULL;
}

void MediaAdapter_play(
    MediaAdapter* self, const char* audioType, const char* filename){
  assert(self != NULL);
  assert(self->advancedMusicPlayer != NULL);
  if(strcasecmp(audioType,"VLC") == 0){
    AdvancedMediaPlayer_playVlc(self->advancedMusicPlayer,filename);
  } else if(strcasecmp(audioType,"MP4") == 0){
    AdvancedMediaPlayer_playMp4(self->advancedMusicPlayer,filename);
  }
}


typedef struct AudioPlayer_ AudioPlayer;
struct AudioPlayer_ {
  MediaPlayer base;
};

void AudioPlayer_init(AudioPlayer* self){
  assert(self != NULL);
  MediaPlayer_init(&self->base);
}

void AudioPlayer_destroy(AudioPlayer* self){
  assert(self != NULL);
  MediaPlayer_destroy(&self->base);
}

void AudioPlayer_play(
    AudioPlayer* self, const char* audioType, const char* filename){
  assert(self != NULL);
  // inbuilt support for mp3 music file
  if(strcasecmp(audioType, "MP3") == 0){
    printf("Playing mp3 file. Name: %s\n", filename);
  }
  else if((strcasecmp(audioType, "VLC") == 0)||(strcasecmp(audioType, "MP4") ==0)){
    MediaAdapter mediaAdapter;
    MediaAdapter_init(&mediaAdapter, audioType);
    MediaAdapter_play(&mediaAdapter,audioType,filename);
    MediaAdapter_destroy(&mediaAdapter);
  }
  else{
    printf("Invalid media. %s format not supported\n", audioType);
  }
}
    


int main(int argc, char* argv[], char* envp[]){
  AudioPlayer audioPlayer;
  AudioPlayer_init(&audioPlayer);
  AudioPlayer_play(&audioPlayer,"mp3","beyond the horizon.mp3");
  AudioPlayer_play(&audioPlayer,"mp4","alone.mp4");
  AudioPlayer_play(&audioPlayer,"vlc","far far away.vlc");
  AudioPlayer_play(&audioPlayer,"avi","mind me.avi");
  AudioPlayer_destroy(&audioPlayer);

  return 0;
}
