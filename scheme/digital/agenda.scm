(load "queue.scm")

(define (agenda)
  ;; agenda implemented as list (Time (T1.Q1) (T2.Q2) ...)
  ;; first item 'Time' of the list is current time of agenda
  ;; subsequent items of the list are pairs (T.Q) where T is a time
  ;; and Q is a queue containing all events scheduled for time T
  ;;
  ;; private data
  (define data (list 0))  ; (0) empty agenda at current time 0
  ;;
  ;; public interface
  (define (disptach m)
    (cond ((eq? m 'isempty?) (isempty?))
          ((eq? m 'time) (car data))        ; current time of agenda
          ((eq? m 'add-item!) add-item!)    ; schedules new event in agenda
          ((eq? m 'read-next!) (read-next!)); removes first event from agenda
          ((eq? m 'propagate!) (propagate!)); executes time simulation
          ((eq? m 'reset!) (reset!))        ; resets agenda
          ((eq? m 'debug) debug)            ; for unit testing only
          (else (display "agenda: unknown operation error\n"))))
  ;;
  ;; private members
  ;;
  (define (reset!) ; resets current time to zero and discards existing schedule
    (set! data (list 0)))
  ;;
  (define (isempty?) (null? (cdr data)))
  ;;
  (define (add-item! T proc)  ; schedules procedure 'proc' for time T
    (let ((time (car data)) (L (cdr data))) ; current time and current list
      (if (< T time)  ; it is possible to schedule proc for immediate execution
        (display "agenda: attempt to schedule procedure in the past error\n")
        (let ((new-list (insert T proc L))) ; returning new list after insertion
          (set! data (cons time new-list))))))
  ;;
  (define (read-next!) ; returns the next scheduled procedure and removes it
    (if (isempty?)
      (display "agenda: attempt to read from empty agenda error\n")
      (let ((first (cadr data)))    ; first time segment (T.Q)
        (let ((T (car first)) (Q (cdr first)))
          (let ((proc (Q 'read!)))   ; proc is read from queue Q
            (set-car! data T)       ; current time of agenda becomes time of proc
            (if (Q 'isempty?) (set-cdr! data (cddr data))) ; remove if Q empty
            proc)))))
  ;;
  ;; Loops recursively until no more procedures are found to execute.
  ;; Since procedures being run will typically schedule further procedures
  ;; inside the agenda, propagate may never terminate.
  (define (propagate!)
    (if (isempty?)
      'done
      (let ((proc (read-next!))) ;reading next procedure from agenda
        (proc)
        (propagate!))))
  ;;
  (define (new-queue T proc)  ; returns a new pair (T.Q) with proc saved in Q
    (let ((Q (queue)))        ; creating new queue
      ((Q 'push!) proc)       ; saving proc to queue
      (cons T Q)))
  ;;
  ;; insert returns a new list from sublist where proc has been scheduled
  ;; for time T. Specifically if time T is already in the sublist, then
  ;; proc is added to the corresponding queue Q of ordered pair (T.Q)
  ;; Otherwise a new ordered pair (T.Q) is created and added to the sublist
  ;; keeping times in increasing order. The procedure proc is added to Q.
  (define (insert T proc sublist)
    (if (null? sublist)
      (list (new-queue T proc))   ; base case
      (let((first (car sublist))) ; sublist not empty, first element (T1.Q1)
        (let ((T1 (car first)) (Q1 (cdr first)))
          (cond ((= T1 T) ; simply add proc to Q1 and return sublist
                 (begin ((Q1 'push!) proc) sublist))
                ((< T T1) ; new time segment inserted and return extended list
                 (let ((new (new-queue T proc)))
                   (cons new sublist)))
                ((< T1 T) ; recursive call, insertion made later
                 (cons first (insert T proc (cdr sublist)))))))))
  ;;
  ;; debug procedure giving access to private state
  (define (debug m)
    (cond ((eq? m 'new-queue) new-queue)
          ((eq? m 'insert) insert)
          ((eq? m 'data) data)
          (else (display "agenda: unknown debug data error\n"))))
  ;;
  ;; returning interface
  disptach)

