(load "global.scm")

(define wire
  ;; should be called 'make-wire'. This is a constructor procedure returning
  ;; object via its message passing interface.
  ;; wire object has three possible states. The current state is encoded by
  ;; the value of 'signal' which can be '(), #f or #t.
  ;; the variable 'owner' is '() if and only if 'signal' is '().
  ;; the variable 'owner' represents the part of the circuit which imposes
  ;; the value of 'signal' to be #t or #f.
  ;;
  ;; private static members
  ;;
  ;; The procedure will be called on a wire's actions list after change of state
  (letrec ((call-each
            (lambda (procs)
              (if (null? procs)
                'done
                (begin
                  ((car procs))  ; exexcuting first procedure in list
                  (call-each (cdr procs))))))
           ;;
           (show-tag
             (lambda (source)
              (cond ((eq? source '()) '())
                    ((symbol? source) source)
                    (else (source 'get-tag)))))
           ;; used in debuggin mode
            (dump
              (lambda (wire value source)
                (if (and (not (global 'unit-test?)) (global 'debug?))
                  (begin
                    (display "Time: ")
                    (display (global 'now))
                    (display "\t   ")
                    (display "Wire: ")
                    (display (wire 'get-tag))
                    (display "\t")
                    (display "Current: ")
                    (display (wire 'get-signal))
                    (display "\t")
                    (display "Owner: ")
                    (display (wire 'owner-tag))
                    (display "\t")
                    (display "Attempt: ")
                    (display value)
                    (display "\t")
                    (display "By: ")
                    (display (show-tag source))
                    (newline))))))
  ;;
  ;; Using construct (define wire .. (let[rec] ...(lambda () ...
  ;; rather than the more readable (define (wire) (define ...
  ;; so as to allow the definition of static members, i.e.
  ;; procedures which are common to all instances of wires
  (lambda()
  ;;
  ;; private data
  (define signal '())   ; three possible values: '() (not set), #f or #t
  (define owner '())    ; '() unless signal is set to #f ot #t
  (define actions '())  ; list of procedures to be executed on change of state
  (define tag '?)       ; tag used mainly for debugging purposes
  (define loop-count 0)
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'get-signal) signal)
          ((eq? m 'set-signal!) set-signal!)
          ((eq? m 'add-action!) add-action!)
          ((eq? m 'set-tag!) set-tag!)  ; setting tag allows better debugging
          ((eq? m 'get-tag) tag)        ; mainly used for debugging
          ((eq? m 'probe!) (probe!))    ; ensures notification of change of state
          ((eq? m 'owner-tag) (show-tag owner))
          ((eq? m 'actions) actions)
          (else (display "wire: unknown operation error\n"))))
  ;;
  ;; private members
  ;;
  ;; add action to the wire's actions list, the effect of which is to notify
  ;; user whenever a change of state occurs.
  (define (probe!)
  (let ((action (lambda ()
                  (display "===========> ")
                  (display "Time: ") (display (global 'now)) (display ", ")
                  (display "wire-") (display tag) (display ": ")
                  (display signal)
                  (display ", owner: ") (display (show-tag owner))
                  (newline))))
    (add-action! action)))
  ;;
  ;; add-action!
  (define (add-action! proc)
    (set! actions (cons proc actions))
    (proc))   ; new action is executed when added to list
  ;;
  ;; set-tag!
  (define (set-tag! t)
    (set! tag t))
  ;;
  ;; set-signal!
  ;; Request for a change of state to 'value' from authority 'source'
  ;; No action is taken unless request actually constitutes a change of state.
  ;; Request is granted if wire not set, and new ownership is set
  ;; Request is granted if coming from source which holds ownership
  ;; Ownership is relinquished if requested signal is '() (unset)
  ;; Granted requests are followed by running all of wire's actions
  ;; which typically notify connected wires of its change of state
  ;; and may also notify user (if the 'probe!' method has been called prior)
  ;; Request from third party is ignored if attempting to set '()
  ;; Request from third party is rejected if attempting to set #f or #t.
  ;; Since such a request constitutes a change of state to #f or #t from
  ;; a current state of #f or #t, it constitutes a contradiction.
  (define (set-signal! value source)
    (dump dispatch value source)           ; comment out to remove debugging
    (if (not (eq? signal value))  ; no action taken unless state changes
      (cond ((eq? owner '())      ; case 1: wire not currently constrained
             ;; This should never happen
             (if(not(eq? signal '()))(display "wire: inconsistent state error\n"))
             ;; signal must be '() while value must be #f or #t at this point
             (set! signal value)  ; accepting new signal value
             (set! owner source)  ; new owner
             (set! loop-count 0)
             (call-each actions))
            ((eq? owner source)   ; case 2: change of state requested by owner
             ;; This should never happen
             (if (eq? signal '())(display "wire: inconsistent state error\n"))
             ;; signal cannot be '() while value may be anything except signal
             (set! signal value)  ; accepting new signal value
             (if (eq? value '()) (set! owner '())); constraint relinquished if '()
             (set! loop-count 0)
             (call-each actions))
            (else     ; case 3: change of state requested by third party
              ;; This should never happen since owner exists
              (if (eq? signal '()) (display "wire: inconsistent state error\n"))
              ;; Attempting to set conflicting value is an error
              (if (not(eq? value '()))
               ((global 'error!) "===========> wire: short circuit error\n")
               ;; experimental line just added
               (begin (set! loop-count (+ 1 loop-count))
                      (if (< loop-count 2) (call-each actions))))))))
               ;)))))
  ;;
  ;; returning public interface
  dispatch)))

