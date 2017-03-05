(define (make-account)
  (let ((balance 0))
    (define (get-balance)
      balance)
    (define (deposit amount)
      (set! balance (+ balance amount))
      balance)
    (define (withdraw amount)
      (deposit (- amount)))
    (lambda args
      (apply
        (case (car args)
          ((get-balance) get-balance)
          ((deposit) deposit)
          ((withdraw) withdraw)
          (else (error "Invalid method!")))
;        (cond ((eq? (car args) 'get-balance) get-balance)
;              ((eq? (car args) 'deposit) deposit)
;              ((eq? (car args) 'withdraw) withdraw)
;              (else (error "Invalid method!")))
        (cdr args)))))


(define my-account (make-account))

(display "balance = ")(display (my-account 'get-balance))(newline)

(my-account 'deposit 100)

(display "balance = ")(display (my-account 'get-balance))(newline)

(my-account 'withdraw 75)

(display "balance = ")(display (my-account 'get-balance))(newline)

(exit 0)
