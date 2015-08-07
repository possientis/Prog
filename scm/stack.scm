(print "stack: module is being loaded")
(define (stack)
  (define pointer '())  ; pointer to top of the stack
  (define (isempty?) (null? pointer))
  (define (push x)      ; pushes x onto stack
    (set! pointer (cons x pointer))
    pointer)
  (define (pop)         ; retrieves top element off the stack
    (cond ((isempty?) "stack: retrieving element from empty stack error")
          (else (let((item (car pointer)))
                  (set! pointer (cdr pointer))
                  item))))
  (define (disptach m)
    (cond ((eq? m 'isempty?) (isempty?))
          ((eq? m 'show) pointer)
          ((eq? m 'pop) (pop))
          ((eq? m 'push) push)
          (else "stack: unknown operation error")))
  (begin (print "stack: code is now running") disptach))
