(load "wire.scm")
(load "binary.scm")

(define (bus size)  ; creates a bus with a number of bits equal to 'size'
  (let ((wire-vect (make-vector size)))
    (define (dispatch m)
      (cond ((eq? m 'get-signal) (get-signal))
            ((eq? m 'set-signal!) set-signal!)
            ((eq? m 'size) size)
            ((eq? m 'get-wire) get-wire)
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
    (define (get-wire bit)  ; 'bit' is index between 0 and size-1
      (vector-ref wire-vect bit))
    ;;
    ;; bus initialization
    (init-bus)
    ;;
    ;; returning public interface
    dispatch))


;; connects bus a b and sum to a ripple-adder
;; c-in and c-out are simple wires (single bits)
(define (ripple-adder a b c-in sum c-out)
  (let ((size (a 'size)))
    (cond ((not (= size (b 'size)))
           (display "bus: ripple-adder: bus size error\n"))
          ((not (= size (sum 'size)))
           (display "bus: ripple-adder: bus size error\n"))
          (else
            (let ((carry (make-vector (+ size 1)))) ; need vector of wires
              (vector-set! carry 0 c-in)            ; first carry wire is input
              (vector-set! carry size c-out)        ; last carry wire is output
              (let loop ((i 1))
                (if (< i size)
                  (begin
                    (vector-set! carry i (wire))    ; new internal wire
                    (loop (+ i 1)))))
              (let loop ((i 0))                     ; looping through all bits
                (if (< i size)
                  (begin
                    (let ((ai ((a 'get-wire) i))
                          (bi ((b 'get-wire) i))
                          (si ((sum 'get-wire) i))
                          (cin (vector-ref carry i))
                          (cout(vector-ref carry (+ i 1))))
                      (full-adder ai bi cin si cout))
                    (loop (+ i 1))))))))))


