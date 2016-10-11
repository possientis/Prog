(define link-node ; constructor
  (let ((let-for-name-encapsulation #t))
    ; object created from data is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'key) (key data))
              ((eq? m 'next) (next data))
              ((eq? m 'value) (value data))
              ((eq? m 'set-next!) (set-next! data))
              ((eq? m 'set-value!) (set-value! data))
              (else (display "link-node: unknown operation error\n")))))
    ;
    (define (key data) (cadr data))
    ;
    (define (value data) (caddr data))
    ;
    (define (next data) (cadddr data))
    ;
    (define (set-next! data)
      (lambda (node) (set-car! (cdddr data) node)))
    ;
    (define (set-value! data)
      (lambda (value) (set-car! (cddr data) value))) 
    ;
    ; returning two arguments constructor
    ;
    (lambda (key value)
      (this (list 'data key value '())))))

 
