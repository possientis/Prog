(define Class-A
  (let ((_static #f))
    ; object built from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'foo) (foo data))
              ((eq? m 'this) (self data))
              (else (error "Class-A: unknown operation error" m)))))
    ;
    ; implementing public interface
    ;
    (define (foo data)
      (display "Class-A::foo is running\n"))
    ; 
    (define (self data)
      (car data))
    ; returning no argument constructor
    ;
    (lambda ()
      (let ((data (cons 'to-be-set-to-this 'other-data)))
        (let ((self (this data)))
          (set-car! data self)
          self)))))

(define x (Class-A))
(x 'foo)
((x 'this) 'foo)


