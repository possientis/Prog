(load "agenda.scm")

(define schedule (agenda))

(define (wire)
  ;; private data
  (let ((signal #f) (actions '()))
    ;; public interface
    (define (dispatch m)
      (cond ((eq? m 'get-signal) signal)
            ((eq? m 'set-signal!) set-signal!)
            ((eq? m 'add-action!) add-action!)
            (else (display "wire: unknown operation error"))))
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

(define (gate-not a b)
  (define (a-action)  ; proc to be executed on signal change by wire a
    (let ((new-value (not (a 'get-signal))))
      (let ((change-b (lambda () ((b 'set-signal!) new-value))))
        ((schedule 'add-item!) 1 change-b))))
  ((a 'add-action!) a-action))

