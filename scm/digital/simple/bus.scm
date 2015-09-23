(load "wire.scm")
(load "binary.scm")

(define (bus size)  ; creates a bus with a number of bits equal to 'size'
  (let ((wire-vect (make-vector size)))
    (define (dispatch m)
      (cond ((eq? m 'get-signal) (get-signal))
            ((eq? m 'set-signal!) set-signal!)
            ((eq? m 'size) size)
            (else (display "bus: unknown operation error\n"i))))
    ;; private methods
    ;;
    (define (init-bus)  ; initilizes vector of wires
      (let loop ((i 0))
        (if (< i size)
          (begin
            (vector-set! wire-vect i (wire))  ; wire-vect[i] = new wire()
            (loop (+ i 1))))))
    ;;
    (define (get-signal)
      (let ((vect (make-vector size)))
        (let loop ((i 0))
          (if (< i size)
            (begin
              (vector-set! vect i ((vector-ref wire-vect i) 'get-signal))
              (loop (+ i 1)))))
        (boolean-vect->integer vect)))
    ;;
    (define (set-signal! num) ;; converts num to binary and sets bus accordingly
      (let ((vect (integer->boolean-vect num size)))
        (let loop ((i 0))
          (if (< i size)
            (begin
              (((vector-ref wire-vect i) 'set-signal!) (vector-ref vect i))
              (loop (+ i 1)))))))
    ;;
    ;; bus initialization
    (init-bus)
    ;;
    ;; returning public interface
    dispatch))


