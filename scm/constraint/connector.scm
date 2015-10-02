; connector object
(define (connector)
  ; private data
  (let ((value #f)        ; #f when no value is set
        (informant #f)    ; #f when no value is set (hence no informant either)
        (constraints '())) ; initial list of constraints is empty
  ; public interface
  (define (dispatch m)
    (cond ((eq? m 'set-value!) set-value!)
          ((eq? m 'forget-value!) forget-value!)
          ((eq? m 'has-value?) (has-value?))
          ((eq? m 'get-value) (get-value))
          ((eq? m 'connect!) connect!)
          (else (display "connector: unknown operation error\n"))))
  ; private members
  (define (set-value! newval user)
    (cond ((not (has-value?))
           (set! value newval)
           (set! informant user)
           (for-each-except user inform-about-value constraints))
          ((not (= value newval))   ; bug lurking, == between doubles
           (error "Contradiction" (list value newval)))
          (else 'ignored)))
  ;
  (define (forget-value! user)
    'ok)
  ;
  (define (has-value?)
    (not (eq? value #f))) ; has a value if (and only if) value is not #f
  ;
  (define (get-value)
    value)                ; simply returns value member
  ;
  (define (connect! new-constraint)
    (if (eq? #f (memq new-constraint constraints)) ; new-constraint not in list
      (set! constraints (cons new-constraint constraints)))
    (if (has-value?)
      (inform-about-value new-constraint))
    'done)
  ;
  (define (inform-about-value constraint)
    (constraint 'process-value!))
  ;
  (define (inform-about-no-value)
    (constraint 'forget-value!))

  ; returning public interface
  dispatch))

(define (for-each-except exception procedure seq)
  (let loop ((seq seq))
    (cond ((null? seq) 'done)
          ((eq? (car seq) exception) (loop (cdr seq)))
          (else (procedure (car seq))
                (loop (cdr seq))))))

; adder object (constraint)
(define (adder a1 a2 sum)
  ; public interface
  (define (this m)
    (cond ((eq? m 'process-value!) (process-value!))
          ((eq? m 'forget-value!) (forget-value!))
          (else (display "adder: unknown operation error\n"))))
  ; private members
  ;
  (define (process-value!)
    (cond ((and (a1 'has-value?) (a2 'has-value?))
           ((sum 'set-value!) (+ (a1 'get-value) (a2 'get-value)) this))
          ((and (a1 'has-value?) (sum 'has-value?))
           ((a2 'set-value!) (- (sum 'get-value) (a1 'get-value)) this))
          ((and (a2 'has-value?) (sum 'has-value?))
           ((a1 'set-value!) (- (sum 'get-value) (a2 'get-value)) this))
          (else 'done)))  ; not enough values have been set
  ;
  (define (forget-value!)
    ((sum 'forget-value!) this)
    ((a1 'forget-value!) this)
    ((a2 'forget-value!) this)
    (process-value!))
  ;
  ; connecting contraint to connectors
  ((a1 'connect!) this)
  ((a2 'connect!) this)
  ((sum 'connect!) this)
  ; returning public interface
  this)

; multiplier object (constraint)
(define (multiplier a1 a2 prod)
  ; public interface
  (define (this m)
    (cond ((eq? m 'process-value!) (process-value!))
          ((eq? m 'forget-value!) (forget-value!))
          (else (display "multiplier: unknown operation error\n"))))
  ; private members
  ;
  (define (process-value!)  ; bug lurking: == 0 for double !!!
    (cond ((and (a1 'has-value?) (= 0 (a1 'get-value)))
           ((prod 'set-value!) 0 this))
          ((and (a2 'has-value?) (= 0 (a2 'get-value)))
           ((prod 'set-value!) 0 this))
          ((and (a1 'has-value?) (a2 'has-value?))
           ((prod 'set-value!) (* (a1 'get-value) (a2 'get-value)) this))
          ((and (a1 'has-value?) (prod 'has-value?))
           ((a2 'set-value!) (/ (prod 'get-value) (a1 'get-value)) this))
          ((and (a2 'has-value?) (prod 'has-value?))
           ((a1 'set-value!) (/ (prod 'get-value) (a2 'get-value)) this))
          (else 'done)))  ; not enough values have been set
  ;
  (define (forget-value!)
    ((prod 'forget-value!) this)
    ((a1 'forget-value!) this)
    ((a2 'forget-value!) this)
    (process-value!))
  ;
  ; connecting contraint to connectors
  ((a1 'connect!) this)
  ((a2 'connect!) this)
  ((prod 'connect!) this)
  ; returning public interface
  this)

; constant object (constraint)
(define (constant const a)
  ; public interface
  (define (this m)
    (cond ((eq? m 'process-value!) (error))
          ((eq? m 'forget-value!) (error))
          (else (error))))
  ;
  (define (error)
    (display "constant: unknown operation error\n"))


  ;
  ; setting constant value
  ((a 'set-value!) const this)

  ; connecting constraint to connector

  (display "still cool?\n")
  ((a 'connect!) this)

  ; returning public interface
  this)

; probe object (constraint)
(define (probe label a)
  ; public interface
  (define (this m)
    (cond ((eq? m 'process-value!) (process-value!))
          ((eq? m 'forget-value!) (forget-value!))
          (else (display "probe: unknown operation error\n"))))
  ; private members
  (define (print-probe value)
    (newline)
    (display "Probe: ")
    (display label)
    (display " = ")
    (display value))
  ;
  (define (process-value!)
    (print-probe (a 'get-value)))
  ;
  (define (forget-value!)
    (print-probe "?"))
  ;
  ; connecting
  ((a 'connect!) this)
  ; returning public interface
  this)
