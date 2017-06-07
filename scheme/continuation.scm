(define the-continuation #f)

;;; a 'continuation' is is an abstraction (some object)
;;; which represents the state of a program flow (where
;;; the meaning of 'state' excludes the heap, but includes
;;; the stack). This object (the continuation) has a single
;;; method 'run' which takes a single argument. Hence, in 
;;; effect, a continuation can be viewed as a function which 
;;; takes a single argument. Syntactically of course, we simply
;;; call (my-continuation my-arg) in order to 'run' the 
;;; continuation with argument 'my-arg'.

;;; (call-with-current-continuation proc)

;;; This is clearly a scheme function call. 
;;; 

(define (test)
  (let ((i 0) (ret #f))
    (set! ret (call-with-current-continuation
      (lambda (k)
        (set! the-continuation k))))
    ; continuation starts here
    (set! i (+ i 1))
    i))


(test)
(the-continuation 0)
(the-continuation "abc")


(define (f k)
  (k 2)
  3)

(display (f (lambda (x) x)))(newline)                 ; 3
(display (call-with-current-continuation f))(newline) ; 2



(exit 0)

