(define hash-lib
  ;;
  ;; static private member
  (let ((prehash
        ;; hack to figure out whether running 'mit-scheme' or 'scm'
        (let ((mit-scheme? (not (= 1 (inexact->exact 1.2)))))
          (lambda (x)
            (if mit-scheme?
              (equal-hash x)          ; value based hash for mit-scheme
              (hash x 1000000000)))))); value based hash for scm
  (lambda ()
    ;;
    ;; public interface
    (define (dispatch m)
      (cond ((eq? m 'prehash) prehash)
            (else (display "hash: unknown operation error\n"))))
    ;;
    ;;returning public interface
    dispatch)))

