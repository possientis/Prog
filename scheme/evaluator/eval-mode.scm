;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-eval-mode)) 
  (begin
    (define included-eval-mode #f)
    (display "loading new-eval")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define __eval-mode__ #f)

(define (set-eval-mode mode)
  (cond ((eq? mode 'strict)   (set! __eval-mode__ 'strict))
        ((eq? mode 'analyze)(set! __eval-mode__ 'analyze))
        ((eq? mode 'lazy)   (set! __eval-mode__ 'lazy))
        (else (error "set-eval-mode: invalid mode argument" mode))))

(set-eval-mode 'strict) ; default

(define (get-eval-mode) 
  (display "check: eval mode requested: ")(display __eval-mode__)(newline)
  __eval-mode__)


))  ; include guard


