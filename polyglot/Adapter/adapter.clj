; Adapter design pattern
(ns adapter
  (:gen-class))

; This the 'target' interface, namely the interface our Adapter
; will need to implement, relying on the 'adaptee' interface
(def MediaPlayer        ; constructor
  (letfn
    ; object created from data is message passing interface
   [(this [data]
     (fn [m]
       (cond (= m :play) (play data)
             :else (println "MediaPlayer: unknown operation error"))))
    ;
    (play [data]
      (println "MediaPlayer::play is not implemented"))]
    ; returning no argument constructor
    (fn [] (this :ignored))))
           
; This is the 'adaptee' interface, of which concrete implementations
; provide the functionality allowing us to implement the adaptor
(def AdvancedMediaPlayer; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :playVlc) (playVlc data)
               (= m :playMp4) (playMp4 data)
               :else (println "AdvancedMediaPlayer: unknown operation error"))))
     ;
     (playVlc [data]
       (println "AdvancedMediaPlayer::playVlc is not implemented"))
     ;
     (playMp4 [data]
       (println "AdvancedMediaPlayer::playMp4 is not implemented"))]
     ; returning no argument constructor
     (fn [] (this :ignored))))

; one implementation of the adaptee interface
(def VlcPlayer          ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :playVlc) (playVlc data)
               (= m :playMp4) (playMp4 data)
               :else (data m))))  ; passing message to base object (= data here)
     ;
     (playVlc [data]
       (fn [filename]
         (println "Playing vlc file. Name:" filename)))
     ;
     (playMp4 [data]
       (fn [filename] :doNothing))]
    ; returning no argument constructor
    (fn [] (this (AdvancedMediaPlayer)))))  ; passing base object as data

; another implementation of the adaptee interface
(def Mp4Player          ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :playVlc) (playVlc data)
               (= m :playMp4) (playMp4 data)
               :else (data m))))  ; passing message to base object (= data here)
     ;
     (playMp4 [data]
       (fn [filename]
         (println "Playing mp4 file. Name:" filename)))
     ;
     (playVlc [data]
       (fn [filename] :doNothing))]
    ; returning no argument constructor
    (fn [] (this (AdvancedMediaPlayer)))))  ; passing base object as data

; Creating adapter class implementing the target interface
(def MediaAdapter       ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :play) (play data)
               :else ((let [[base player] data] base) 'm)))) ; passing to base
     ;
     (play [[base player]]
       (fn [audioType filename]
         (cond (= (.toUpperCase audioType) "VLC") ((player :playVlc) filename)
               (= (.toUpperCase audioType) "MP4") ((player :playMp4) filename)
               :else :doNothing)))]
    ; returning single argument constructor
    (fn [audioType]
      (cond (= (.toUpperCase audioType) "VLC") (this [(MediaPlayer) (VlcPlayer)])
            (= (.toUpperCase audioType) "MP4") (this [(MediaPlayer) (Mp4Player)])
               :else nil))))

; Creating new class of MediaPlayer which uses our adaptor (optional)
(def AudioPlayer        ; constructor
  (letfn
    ; object created from data is message passing interface
    [(this [data]
       (fn [m]
         (cond (= m :play) (play data)
               :else (data m))))  ; passing message to base object (= data)
     ;
     (play [data]
       (fn [audioType filename]
         (cond  (= (.toUpperCase audioType) "MP3")
                (println "Playing mp3 file. Name:" filename)
                (or (= (.toUpperCase audioType) "VLC")
                    (= (.toUpperCase audioType) "MP4"))
                (let [adapter (MediaAdapter audioType)]
                  ((adapter :play) audioType filename))
                :else(println "Invalid media." audioType "format not supported"))))]
    ; returning no argument constructor
    (fn [] (this (MediaPlayer)))))

; We can now use the AudioPlayer to play different types of audio formats
(defn -main []
(def player (AudioPlayer))
((player :play) "mp3" "beyond the horizon.mp3")
((player :play) "mp4" "alone.mp4")
((player :play) "vlc" "far far away.vlc")
((player :play) "avi" "mind me.avi"))

;(-main)





