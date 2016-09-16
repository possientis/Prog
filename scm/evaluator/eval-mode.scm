;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-eval)) 
  (begin
    (define included-new-eval #f)
    (display "loading new-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define __eval-mode__ #f)

(define (set-eval-mode mode)
  (cond ((eq? mode 'eval)   (set! __eval-mode__ 'eval))
        ((eq? mode 'analyze)(set! __eval-mode__ 'analyze))
        ((eq? mode 'lazy)   (set! __eval-mode__ 'lazy))
        (else (error "set-eval-mode: invalid mode argument" mode))))

(set-eval-mode 'eval) ; default

(define (get-eval-mode) __eval-mode__)



))  ; include guard


