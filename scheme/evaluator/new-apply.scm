;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-apply)) 
  (begin
    (define included-new-apply #f)
    (display "loading new-apply")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (new-apply proc args)
  (let ((mode (get-eval-mode)))
    (cond ((eq? mode 'strict) (strict-apply proc args))
          ((eq? mode 'lazy)   (lazy-apply proc args))
          ((eq? mode 'analyze)(analyze-apply proc args))
          (else "new-apply: invalid evaluation mode" mode))))



))  ; include guard

