(define complex
  ;;
  (lambda (real imag)
  ;; private data
  (define data (cons real imag))
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'real) (car data))
          ((eq? m 'imag) (cdr data))
          ((eq? m 'mod) (modulus))
          ((eq? m 'angle)(theta))
          ((eq? m 'show) (show))
          (else (display "complex: unknwon operation error\n"))))
  ;; private members
  ;;
  (define (show)
    (display (car data)) (display "+")(display (cdr data))(display "i"))
  ;;
  (define (modulus)
    (let ((x (car data)) (y (cdr data)))
      (sqrt (+ (* x x) (* y y)))))
  ;;
  (define (theta)
    (atan (cdr data) (car data)))
  ;;
  ;; returning public interface
  dispatch))

(define complex-utils
  ;; static private members
  ;;
  (let ((complex-add
          (lambda (x y)
            (complex (+ (x 'real) (y 'real))
                     (+ (x 'imag) (y 'imag)))))
        (complex-sub
          (lambda (x y)
            (complex (- (x 'real) (y 'real))
                     (- (x 'imag) (y 'imag)))))
        (complex-mul
          (lambda (x y)
            (complex (- (* (x 'real) (y 'real))
                        (* (x 'imag) (y 'imag)))
                     (+ (* (x 'real) (y 'imag))
                        (* (x 'imag) (y 'real))))))
        )
    (lambda ()
      (define (dispatch m)
        (cond ((eq? m '+) complex-add)
              ((eq? m '-) complex-sub)
              ((eq? m '*) complex-mul)
              (else (display "complex-utils: unknown operation error\n"))))
      ;;
      ;; returning interface
      dispatch)))


