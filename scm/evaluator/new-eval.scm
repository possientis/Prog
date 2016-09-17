;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-eval)) 
  (begin
    (define included-new-eval #f)
    (display "loading new-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; this will speed up the code, but reasoning on semantics more difficult
(define (new-eval2 exp . arg)
  (let ((env (if (null? arg) global-env (car arg))))
    (let ((analyzed (analyze exp)))
      (analyzed env))))

(define (new-eval exp . arg)
  (if (null? arg) (strict-eval exp) (strict-eval exp (car arg))))


))  ; include guard.
