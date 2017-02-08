(define mode 'strict)

(define load-proc 
  (cond ((eq? 'strict mode) strict-load)
        ((eq? 'analyze mode) analyze-load)
        ((eq? 'lazy mode) lazy-load)
        (else "error: load-proc: unknown evaluation mode")))

(define eval-proc 
  (cond ((eq? 'strict mode) strict-eval)
        ((eq? 'analyze mode) analyze-eval)
        ((eq? 'lazy mode) lazy-eval)
        (else "error: eval-proc: unknown evaluation mode" mode)))

(define (do-load filename)
  (apply load-proc (list filename)))

(define (do-run expr)
  (apply eval-proc (list expr)))


