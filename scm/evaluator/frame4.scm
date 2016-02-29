(require 'hash-table)

(define frame4
  (let ((_static #f))
    ; object created is message passing interface
    (define (this data)
      (lambda (m)
        (cond ((eq? m 'empty?) (empty? data))
              ((eq? m 'insert!)(insert! data))
              ((eq? m 'delete!)(delete! data))
              ((eq? m 'find)   (search data))
              ((else (error "frame4: unknown operation error: " m))))))
    ;
    ; implementation of public interface
    ;
    (define (empty? data) #f)     ; TBI
    ;
    (define (insert! data)
      (lambda (key value) 'tbi))  ; TBI
    ;
    (define (delete! data)
      (lambda (key) 'tbi))        ; TBI
    ;
    (define (search data) 
      (lambda (key) #f))          ; TBI
    ;
    ; returning no argument constructor
    ;
    (lambda () (this 'ignored))))


