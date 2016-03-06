; basic (linear) dictionary implementation.
(require 'object->string)
;
; 1. insert! will overwrite value of existing key, rather than insert duplicate key
; 2. find returns a pair (key . value) from key, or expression #f if key not found
; 3. delete! will remove pair (key . value) from frame
;
(define frame2           ; constructor
   (let ((_static #f))
     ; object built from data is message passing interface
     (define (this data)
       (lambda (m)
         (cond ((eq? m 'empty?)  (empty? data)) 
               ((eq? m 'insert!) (insert! data))
               ((eq? m 'delete!) (delete! data))
               ((eq? m 'find)    (search data))  ; 'find' is primitive
               ((eq? m 'to-string) (to-string data))
               (else (error "frame2: unknown operation error: " m)))))
     ;
     ; implementation of public interface
     ;
     (define (empty? data)
       (equal? (cdr data) '()))
     ;
     (define (insert! data)
       (lambda (key val)
         (let ((found ((find-first data) key)))
           (if (eq? #f found) ; key not already present
             (set-cdr! data (cons (cons key val) (cdr data)))
             ; else, key already present, simply overwrites value
             (let ((pair (car found)))
               (set-cdr! pair val))))))
     ;
     (define (delete! data)
       (lambda (key)
         (let ((new-pairs '()))
           (let loop ((pairs (cdr data)))
             (if (null? pairs)
               (set-cdr! data new-pairs) ; changing frame data
               ; else
               (begin
                 (if (not (equal? key (caar pairs)))
                   (set! new-pairs (cons (car pairs) new-pairs)))
                 (loop (cdr pairs))))))))
     ;
     (define (search data) ; returns pair (key . val) or #f
       (lambda (key)
         (let ((found ((find-first data) key)))
           (if (eq? #f found) ; key not already present
             #f
             ; else
             (car found)))))
     ;
     (define (to-string data)
       (let loop ((pairs (cdr data)) (out "{") (start #t))
         (if (null? pairs)
           (string-append out "}")
           (let ((new-out (string-append
                            out
                            (if start "" ", ")
                            (object->string (caar pairs))
                            ": "
                            (object->string (cdar pairs)))))
             (loop (cdr pairs) new-out #f)))))
     ; private helper function
     ;
     (define (find-first data)
       (lambda (key)  ; returns list 'pairs' where key = (caar pairs), or #f
         (define (loop pairs)
           (if (null? pairs)
             #f ; key not present
             (if (equal? key (caar pairs))
               pairs
               (loop (cdr pairs)))))
         (loop (cdr data))))
     ;
     ; returning no argument constructor
     ;
     ; frame is implemented as a pair ('frame . data) where
     ; data is a pair (keys . vals) where keys and vals are
     ; two lists of equal length. Very basic dictionary with
     ; linear search complexity. Obviously inefficient.
     (lambda () (this (cons 'frame '())))))



