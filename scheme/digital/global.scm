(load "agenda.scm")

;; object encapsulating global variables and free procedures
;; created to avoid  polluting global name space.
(define make-global-object
  ;;
  ;; static private data
  (let ((debug? #f)             ; whether in debug mode
        (unit-test? #f)         ; whether unit-test code is running
        (error-count 0)         ; counter allowing to check expected errors
        (main-agenda (agenda))) ; creating global agenda for time/event simulation
  ;;
  ;; irregular indentation
  ;; using construct (define make-global-object (let ...(lambda () ...
  ;; as opposed to more readable (define (make-global-object) (define ...)
  ;; to make the data static, i.e. common to every instance of object
  (lambda()
  ;;
  ;; private procedures
  ;;
  (define (error! m)
    ;; displays error message m unless in unit-testing mode
    ;; increments error count
    (if (not unit-test?) (display m))
    (set! error-count (+ 1 error-count)))
  ;;
  (define (add-event! time-delay proc)
    ;; schedules procedure 'proc' on main-agenda
    (let ((time (+ time-delay (main-agenda 'time))))
      ((main-agenda 'add-item!) time proc)))
  ;;
  ;;  public interface
  (define (dispatch m)
    (cond ((eq? m 'unit-test?) unit-test?)
          ((eq? m 'unit-test-true!)  (set! unit-test? #t))
          ((eq? m 'unit-test-false!) (set! unit-test? #f))
          ((eq? m 'debug?) debug?)
          ((eq? m 'debug-true!)  (set! debug? #t))
          ((eq? m 'debug-false!) (set! debug? #f))
          ((eq? m 'error-count) error-count)
          ((eq? m 'error-count-reset!) (set! error-count 0))
          ((eq? m 'error!) error!)
          ((eq? m 'now) (main-agenda 'time))
          ((eq? m 'time-reset!) (main-agenda 'reset!))
          ((eq? m 'propagate!) (main-agenda 'propagate!))
          ((eq? m 'add-event!) add-event!)
          (else (display "global: unknown operation error\n"))))
  ;;
  ;; returning interface
  dispatch)))


(define global (make-global-object))


