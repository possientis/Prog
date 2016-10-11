; Adapter design pattern

; This the 'target' interface, namely the interface our Adapter
; will need to implement, relying on the 'adaptee' interface
(define MediaPlayer   ; constructor
  (let ((_static #f)) ; dummy field, achieves name encapsulation and readability
    ; object built from data is a message passing interface
    (define (this data) ; data ignore here
      (lambda (m)
        (cond ((eq? m 'play) (display "MediaPlayer::play is not implemented\n"))
              (else (display "MediaPlayer: unknown operation error\n")))))
    ; returning no argument constructor
    (lambda () (this 'ignored))))

; This is the 'adaptee' interface, of which concrete implementations
; provide the functionality allowing us to implement the adaptor
(define AdvancedMediaPlayer ; constructor
  (let ((_static #f))       ; dummy field, achieves name encapsulation
    ; object built from data is message passing interface
    (define (this data) ; data ignore here
      (lambda (m)
        (cond ((eq? m 'playVlc) 
               (display "AdvancedMediaPlayer::playVlc is not implemented\n"))
              ((eq? m 'playMp4)
               (display "AdabcedMediaPlayer::playMp4 is not implemented\n"))
              (else (display "AdvancedMediaPlayer: unkown operation error\n")))))
    ; returning no argument constructor
    (lambda () (this 'ignored))))

; one implementation of the adaptee interface
(define VlcPlayer     ; constructor
  (let ((_static #f)) ; dummy field, achieves name encapsulation and readability 
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'playVlc) (playVlc data))
              ((eq? m 'playMp4) (playMp4 data))
              (else ((base data) m))))) ; calling operation on base object
    (define (base data)
      data) ; data is simply base object
    (define (playVlc data)  ; data is ignored
      (lambda (filename)
        (display "Playing vlc file. Name: ")
        (display filename)(newline)))
    (define (playMp4 data)  ; data is ignored
      (lambda (filename)
        'doNothing))
    ; returning no argument constructor
    (lambda() (this (AdvancedMediaPlayer))))) ; data is simply base object

; another implementation of the adaptee interface
(define Mp4Player     ; constructor
  (let ((_static #f)) ; dummy field, achieves name encapsulation and readability 
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'playVlc) (playVlc data))
              ((eq? m 'playMp4) (playMp4 data))
              (else ((base data) m))))) ; calling operation on base object
    (define (base data)
      data) ; data is simply base object
    (define (playMp4 data)  ; data is ignored
      (lambda (filename)
        (display "Playing mp4 file. Name: ")
        (display filename)(newline)))
    (define (playVlc data)  ; data is ignored
      (lambda (filename)
        'doNothing))
    ; returning no argument constructor
    (lambda() (this (AdvancedMediaPlayer))))) ; data is simply base object


; Creating adapter class implementing the target interface
(define MediaAdapter  ; constructor
  (let ((_static #f)) ; dummy field
    ; object built from data is message passing interface
    (define (this data)
      (init data) ; initializing object
      (lambda (m)
        (cond ((eq? m 'play) (play data))
              (else ((base data) m))))) ; calling operation on base object
    (define (init data)
      (cond ((equal? (string-upcase (cdr data)) "VLC")(set-cdr! data (VlcPlayer)))
            ((equal? (string-upcase (cdr data)) "MP4")(set-cdr! data (Mp4Player)))
            (else 'doNothing)))
    (define (base data)
      (car data)) ; data will be a pair (base, advancedMusicPlayer)
    (define (play data)
      (lambda (audioType filename)
        (cond ((equal? (string-upcase audioType) "VLC")
               (((cdr data) 'playVlc) filename))  ; (cdr data) is a VlcPlayer
              ((equal? (string-upcase audioType) "MP4")
               (((cdr data) 'playMp4) filename))
              (else 'doNothing))))
    ; returning single argument constructor
    ; data is coded as pair (base , audioType) where audioType is string
    ; which will be replaced by the corresponding advancedMusicPlayer
    (lambda (audioType)
      (this (cons (MediaPlayer) audioType)))))

; Creating new class of MediaPlayer which uses our adaptor (optional)
(define AudioPlayer   ; constructor
  (let ((_static #f)) ; dummy field
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'play) (play data))
              (else ((base data) m))))) ; calling operation on base object
    (define (base data)
      data) ; data will be just base object 
    (define (play data)
      (lambda (audioType filename)
        (cond ((equal? (string-upcase audioType) "MP3")
               ; inbuilt support for mp3 music file
               (display "Playing mp3 file. Name: ")
               (display filename)(newline))
              ((or (equal? (string-upcase audioType) "VLC")
                   (equal? (string-upcase audioType) "MP4"))
               (let ((adapter (MediaAdapter audioType)))
                 ((adapter 'play) audioType filename)))
              (else (display "Invalid media. ")
                    (display audioType)
                    (display " format not supported")(newline)))))
    ; returning no argument constructor
    (lambda () (this (MediaPlayer)))))


; We can now use the AudioPlayer to play different types of audio formats
(define player (AudioPlayer))
((player 'play) "mp3" "beyond the horizon.mp3")
((player 'play) "mp4" "alone.mp4")
((player 'play) "vlc" "far far away.vlc")
((player 'play) "avi" "mind me.avi")

(exit 0)
