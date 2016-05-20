;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-repl)) 
  (begin
    (define included-repl #f)
    (display "loading repl")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(load "eval.scm")
(load "analyze.scm")

(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (newline)(display ">")
  (let ((input (read)))
    (let ((output1 (eval input global-env))
          (output2 ((analyze input) global-env)))
      (announce-output output-prompt)
      (user-print1 output1)
      (user-print2 output2)))
  (driver-loop))

(define (prompt-for-input str)
  (newline)(display str))

(define (announce-output str)
  (display str)(newline))

(define (user-print1 object)
  (display "eval:         ")
  (if (compound-procedure? object)
    (display (list 'compound-procedure
                   (procedure-parameters object)
                   (procedure-body object)
                   '<procedure-env>))
    (display object))(newline))

(define (user-print2 object)
  (display "analyze:      ")
  (if (compound-procedure? object)
    (display (list 'compound-procedure
                   (procedure-parameters object)
                   (procedure-body object)
                   '<procedure-env>))
    (display object))(newline))


(driver-loop)


))  ; include guard
