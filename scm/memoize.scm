(load "dict.scm")

(define (memoize f)
  ;;
  ;;private data
  (let ((dict (dictionary)))
  ;;
  ;; public interface
  (define (dispatch m)
    (let ((out ((dict 'find) m))) ; searching argument in dictionary
      (if (eq? #f out)            ; argument not in dictionary, first call
        (let ((res (f m)))        ; calling function f on argument m
          ((dict 'insert!) m res) ; storing result for future call
          (display "Function called and result stored in dictionary\n")
          res)                    ; returning result
        (begin
          (display "Returning result from dictionary\n")
          (cdr out)))))           ; returning result from dictionary
  dispatch))

(define (fib n)                   ; a very inefficient function
  (cond ((< n 0) #f)
        ((= n 0) 0)
        ((= n 1) 1)
        (else (+ (fib (- n 1)) (fib (- n 2))))))

(define memo-fib
  (memoize (lambda (n)
            (cond ((< n 0) #f)
                  ((= n 0) 0)
                  ((= n 1) 1)
                  (else (+ (memo-fib (- n 1)) (memo-fib (- n 2))))))))


