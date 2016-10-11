(load "agenda.scm")

(define schedule (agenda))

;; creates wire object, handled via returned interface
(define (wire)
  ;; private data
  (let ((signal #f) (actions '()))
    ;; public interface
    (define (dispatch m)
      (cond ((eq? m 'get-signal) signal)
            ((eq? m 'set-signal!) set-signal!)
            ((eq? m 'add-action!) add-action!)
            (else (display "wire: unknown operation error\n"))))
    ;; private methods
    ;;
    (define (call-each procs)
      (if (null? procs)
        'done
        (begin
          ((car procs))   ; running procedure (car procs)
          (call-each (cdr procs)))))
    ;;
    (define (add-action! proc)
      (set! actions (cons proc actions))  ; adding proc to list
      (proc)) ; new action is run immediately when added to list
    ;;
    (define (set-signal! value)
      (if (not (eq? signal value))
        (begin
          (set! signal value)
          (call-each actions))
        'done))
    ;; returning public interface
    dispatch))

;; connects wire 'a' to a probe. 'tag' is a symbol used for notification display
(define (probe a tag)
  (define (a-action)  ; proc to be executed on signal change by wire 'a'
    (let ((time (schedule 'time)) (signal (a 'get-signal)))
      (display "time = ")
      (display time)
      (display ": wire ")
      (display tag)
      (display " is set to value = ")
      (display signal)
      (newline)))
  ((a 'add-action!) a-action))


;; connects wires 'in' and 'out' to an inverter
(define (gate-not in out)
  (define time-delay 1)
  (define (in-action)  ; proc to be executed on signal change by wire 'in'
    (let ((new-value (not (in 'get-signal)))
          (time (+ time-delay (schedule 'time))))
      (let ((change-out (lambda () ((out 'set-signal!) new-value))))
        ((schedule 'add-item!) time change-out))))
  ((in 'add-action!) in-action))

;; connects wire 'in-1', 'in-2' and 'out' to a logical 'or' gate
(define (gate-or in-1 in-2 out)
  (define time-delay 2)
  (define (in-action) ; proc to be executed on signal change by wire in-1 or in-2
    (let ((new-value (or (in-1 'get-signal) (in-2 'get-signal)))
          (time (+ time-delay (schedule 'time))))
      (let ((change-out (lambda () ((out 'set-signal!) new-value))))
        ((schedule 'add-item!) time change-out))))
  ((in-1 'add-action!) in-action)
  ((in-2 'add-action!) in-action))

;; connects wire 'in-1', 'in-2' and out to a logical 'and' gate
(define (gate-and in-1 in-2 out)
  (define time-delay 2)
  (define (in-action) ; proc to be executed on signal change by wire in-1 or in-2
    (let ((new-value (and (in-1 'get-signal) (in-2 'get-signal)))
          (time (+ time-delay (schedule 'time))))
      (let ((change-out (lambda () ((out 'set-signal!) new-value))))
        ((schedule 'add-item!) time change-out))))
  ((in-1 'add-action!) in-action)
  ((in-2 'add-action!) in-action))

;; connects wires a,b, sum, carry to half-adder component
(define (half-adder a b sum carry)
  (let ((w1 (wire)) (w2 (wire)))
    (gate-or a b w1)
    (gate-and a b carry)
    (gate-not carry w2)
    (gate-and w1 w2 sum)))

(define (full-adder a b c-in sum c-out)
  (let ((s (wire)) (c1 (wire)) (c2 (wire)))
    (half-adder c-in b s c1)
    (half-adder s a sum c2)
    (gate-or c1 c2 c-out)))



