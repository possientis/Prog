(define rat       ; creates rational
  ;;
  (lambda (numer denom)
  ;; private data
  (define data
    (let ((g (gcd numer denom)))
      (cons (/ numer g) (/ denom g))))
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'numer) (car data))
          ((eq? m 'denom) (cdr data))
          ((eq? m 'show) (show))
          (else (display "rat: unknown operation error\n"))))
  ;; private members
  ;;
  (define (show)
    (display (car data)) (display "/") (display (cdr data)))
  ;;
  ;; returning public interface
  dispatch))


(define rat-utils
  ;; static private members
  ;;
  (let ((rat-eq?
          (lambda (x y)
            (= (* (x 'numer) (y 'denom)) (* (x 'denom) (y 'numer)))))
        ;;
        (rat-add
          (lambda (x y)
            (rat (+ (* (x 'numer) (y 'denom)) (* (y 'numer) (x 'denom)))
                 (* (x 'denom) (y 'denom)))))
        ;;
        (rat-sub
          (lambda (x y)
            (rat (- (* (x 'numer) (y 'denom)) (* (y 'numer) (x 'denom)))
                 (* (x 'denom) (y 'denom)))))
        ;;
        (rat-mul
          (lambda (x y)
            (rat (* (x 'numer) (y 'numer)) (* (x 'denom) (y 'denom)))))
        ;;
        (rat-div
          (lambda (x y)
            (rat (* (x 'numer) (y 'denom)) (* (x 'denom) (y 'numer)))))
        )
  (lambda ()
    (define (dispatch m)
      (cond ((eq? m '=) rat-eq?)
            ((eq? m '+) rat-add)
            ((eq? m '-) rat-sub)
            ((eq? m '*) rat-mul)
            ((eq? m '/) rat-div)
            (else (display "rat-utils: unknown operation error\n"))))
    ;;
    ;; returning interface
    dispatch)))
