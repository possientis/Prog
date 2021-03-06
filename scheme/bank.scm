(define body
  '(if (<= amount balance) (begin (set! balance (- balance amount)) balance) (display "insufficient funds\n")))


(define (make-account1 balance)
  (lambda (amount)
    (if (<= amount balance)
      (begin (set! balance (- balance amount))
             balance)
      (display "insufficient funds\n"))))

(define (make-account2 init-balance)
  ((lambda (balance)
     (lambda (amount)
       (if (<= amount balance)
         (begin (set! balance (- balance amount))
                balance)
         (display "insufficient funds\n")))) init-balance))

;(define (make-account2 init-balance)
;  (let ((balance init-balance))
;    (lambda (amount)
;      (if (<= amount balance)
;        (begin (set! balance (- balance amount))
;               balance)
;        (display "insufficient funds\n")))))

(define (make-account3 init-balance)
  (define balance init-balance)
  (lambda (amount)
    (if (<= amount balance)
      (begin (set! balance (- balance amount))
             balance)
      (display "insufficient funds\n"))))


(define w1 (make-account1 100))
(define w2 (make-account2 100))
(define w3 (make-account3 100))
