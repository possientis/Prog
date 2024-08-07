;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-frame1)) 
  (begin
    (define included-frame1 #f)
    (display "loading frame1")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


; basic (linear) dictionary implementation.
(require 'object->string)
;
; 1. insert! will overwrite value of existing key, rather than insert duplicate key
; 2. find returns a pair (key . value) from key, or expression #f if key not found
; 3. delete! will remove pair (key . value) from frame
;
(define frame1           ; constructor
   (let ((_static #f))
     ; object built from data is message passing interface
     (define (this data)
       (lambda (m)
         (cond ((eq? m 'empty?)  (empty? data)) 
               ((eq? m 'insert!) (insert! data))
               ((eq? m 'delete!) (delete! data))
               ((eq? m 'find)    (search data)); 'find' is primitive name
               ((eq? m 'to-string) (to-string data))
               ((else (error "frame1: unknown operation error: " m))))))
     ;
     ; implementation of public interface
     ;
     (define (empty? data)
       (equal? (cdr data) (cons '() '())))
     ;
     (define (insert! data)
       (lambda (key val)
         (let ((found ((find-first data) key)))
           (if (eq? #f found) ; key not already present
             (let ((keys (data-keys data)) (vals (data-values data)))
               (set-cdr! data (cons (cons key keys) (cons val vals))))
             ; else, key already present, simply overwrites value
             (let ((vals (cdr found)))
               (set-car! vals val))))))
     ;
     (define (delete! data)
       (lambda (key)
         (let ((new-keys '()) (new-vals '()))
           (let loop ((keys (data-keys data)) (vals (data-values data)))
             (if (null? keys)
               (set-cdr! data (cons new-keys new-vals)) ; changing frame data
               ; else
               (begin
                 (if (not (equal? key (car keys)))
                   (begin
                     (set! new-keys (cons (car keys) new-keys))
                     (set! new-vals (cons (car vals) new-vals))))
                 (loop (cdr keys) (cdr vals))))))))
     ;
     (define (search data) ; returns pair (key . val) or #f
       (lambda (key)
         (let ((found ((find-first data) key)))
           (if (eq? #f found) ; key not already present
             #f
             ; else
             (cons (caar found) (cadr found))))))
     ;
     (define (to-string data)
       (let loop ((keys (data-keys data)) 
                  (vals (data-values data)) (out "{") (start #t))
         (if (null? keys)
           (string-append out "}")
           (let ((new-out (string-append
                            out
                            (if start "" ", ")
                            (object->string (car keys))
                            ": "
                            (object->string (car vals)))))
             (loop (cdr keys) (cdr vals) new-out #f)))))
     ; private helper function
     ;
     (define (data-keys data)
       (cadr data))
     ;
     (define (data-values data)
       (cddr data))
     ;
     (define (find-first data)
       (lambda (key)  ; returns pair (keys . vals) or #f where key = (car keys)
         (define (loop keys vals)
           (if (eq? '() keys)
             #f ; key not present
             (if (equal? (car keys) key)
               (cons keys vals)
               (loop (cdr keys) (cdr vals)))))
         (loop (data-keys data) (data-values data))))
     ;
     ; returning no argument constructor
     ;
     ; frame is implemented as a pair ('frame . data) where
     ; data is a pair (keys . vals) where keys and vals are
     ; two lists of equal length. Very basic dictionary with
     ; linear search complexity. Obviously inefficient.
     (lambda () (this (cons 'frame (cons '() '()))))))

))  ; include guard


