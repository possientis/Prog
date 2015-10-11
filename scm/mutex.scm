; primitive test-and-set! non-atomic implemenation
(define (test-and-set! cell)  ; cell expected to be form (#t) or (#f)
  (let ((val (car cell)))
    (set-car! cell #t)
    val))


(define (mutex) ; create mutex object
  ;
  ;private data
  (let ((cell (list #f))) ; mutex initially unlocked
  ;
  ; public interface
  (define (dispatch m)
    (cond ((eq? m 'acquire) (acquire))
          ((eq? m 'release) (release))
          (else (display "mutex: unknown operation error\n"))))
  ;
  (define (acquire)
    (display "attempting to acquire mutex\n")
    (if (test-and-set! cell) (acquire)) ; busy waiting
    (display "mutex acquired\n")
    ; some implementation
    'done)
  ;
  (define (release)
    (display "releasing mutex\n")
    (set-car! cell #f)
    ; some implementation
    'done)
  ;
  ;returning interface
  dispatch))


(define (serializer)  ; creates serializer object
  ;
  ; private data
  (let ((mutex_ (mutex))) ; creating mutex for serializer
    ;
    ; public interface
    (define (serialize proc) ; serializer simply acts on proc
      (define (serial-proc . args)
        (mutex_ 'acquire)
        (let ((val (apply proc args)))
          (mutex_ 'release)
          val))
      serial-proc)
    ;
    ; returning interface
    serialize))

; some function
(define (f x) (* x x))

(define s (serializer))   ; instanciating serializer

(define g (s f))  ; g is serialized version of f

(display (g 2))
(newline)








