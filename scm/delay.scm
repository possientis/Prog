#!/usr/bin/scm
(require 'macro)  ; 'syntax-rules unbound otherwise

; implementation of force simple
(define (force object)  ; simply calling object
  (object))

; this is how delay is implemented
; see r5rs.pdf page 32
(define-syntax delay
  (syntax-rules
    ()
    ((delay expression)
     (make-promise (lambda () expression)))))

(define (make-promise proc)
  (let ((ready? #f)(result #f))
    (lambda ()
      (if ready?
        result
        (let ((x (proc)))
          ; here is the key point from r5rs.pdf
          ; "A promise may refer to its own value.
          ; Forcing such a promise may cause the
          ; promise to be forced a second time
          ; before the value of the first force
          ; has been computed."
          ;
          ; Normally, you would expect the code
          ; simply to return 'x at this stage
          ; (after setting ready? and result)
          ; However, the call to proc may be recursive
          ; and may have side effects. So if we
          ; want make sure forcing always returns
          ; the same value, we need to test once
          ; more for ready?
          (if ready?
            result
            (begin
              (set! ready? #t)
              (set! result x)
              result)))))))

; compare with naive version
(define-syntax naive-delay
  (syntax-rules
    ()
    ((naive-delay expression)
     (make-naive-promise (lambda() expression)))))

; compare with naive promise
(define (make-naive-promise proc)
  (let ((ready? #f)(result #f))
    (lambda()
      (if ready?
        result
        (let ((x (proc)))
          (set! ready? #t)
          (set! result x)
          result)))))

; can't work out example where make-promise
; vs make-naive-promise matters.


(exit 0)
