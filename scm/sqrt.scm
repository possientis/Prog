(newline)
(display "Trial square root function is 'sqr'\n")
(display "Native square root function is 'sqrt'\n")
;;
(define (sqr x)
  ;;
  (define (good-enough? guess)
    (< (abs (- (square guess) x)) 0.00000001))
  ;;
  (define (improve guess)
    (average guess (/ x guess)))
  ;;
  (let loop ((guess 1.0))
    (display "guess = ")
    (display guess)
    (display "\n")
    (if (good-enough? guess)
      guess
      (loop (improve guess)))))
;;
(define (average x y)
  (/ (+ x y) 2))
;;
(define (square x)
  (* x x))
;
