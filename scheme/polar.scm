(define polar
  ;;
  (lambda (modulus theta)
  ;; private data
  (define data (cons modulus theta))
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'real) (real))
          ((eq? m 'imag) (imag))
          ((eq? m 'mod) (car data))
          ((eq? m 'angle) (cdr data))
          ((eq? m 'show)(show))
          ((eq? m 'type) 'polar)
          (else (display "polar: unknown operation error\n"))))
  ;; private members
  ;;
  (define (show)
    (display real)(display "+")(display imag)(display "i"))
  ;;
  (define (real)
    (* (car data) (cos (cdr data))))
  ;;
  (define (imag)
    (* (car data) (sin (cdr data))))
  ;;
  ;; returning public interface
  dispatch))

(define polar-utils
  ;; static private members
  ;;
  (let ((polar-add
          (lambda (x y)
            (let ((u (+ (x 'real) (y 'real)))
                  (v (+ (x 'imag) (y 'imag))))
              (polar
                (sqrt (+ (* u u) (* v v)))
                (atan v u)))))
        (polar-sub
          (lambda (x y)
            (let ((u (- (x 'real) (y 'real)))
                  (v (- (x 'imag) (y 'imag))))
              (polar
                (sqrt (+ (* u u) (* v v )))
                (atan v u)))))
        (polar-mul
          (lambda (x y)
            (polar (* (x 'mod) (y 'mod))
                   (+ (x 'angle) (y 'angle)))))
        (polar-div
          (lambda (x y)
            (polar (/ (x 'mod) (y 'mod))
                   (- (x 'angle) (y 'angle)))))
        (polar-eq?
          (lambda (x y)
           (and
             (< (abs (- (x 'real) (y 'real))) 0.0000000001)
             (< (abs (- (y 'imag) (y 'imag))) 0.0000000001))))
        )
    (lambda ()
      (define (dispatch m)
        (cond ((eq? m '+) polar-add)
              ((eq? m '-) polar-sub)
              ((eq? m '*) polar-mul)
              ((eq? m '/) polar-div)
              ((eq? m '=) polar-eq?)
              (else (display "polar-utils: unkown operation error\n"))))
      ;;
      ;; returning interface
      dispatch)))
