;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-eval)) 
  (begin
    (define included-new-eval #f)
    (display "loading new-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(define (new-eval exp . arg)
  (display "check1: inside new-eval ...")(newline)
  (let ((env (if (null? arg) global-env (car arg))))
    (let ((mode (get-eval-mode)))
      (cond ((eq? mode 'strict) (strict-eval exp env))
            ((eq? mode 'lazy)   (lazy-eval exp env))
            ((eq? mode 'analyze)((analyze exp) env))
            (else "new-eval: invalid evaluation mode" mode)))))


))  ; include guard.
