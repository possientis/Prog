(load "wire.scm")

;; This connects a wire to a signal source.
;; The source signal may be #f #t or unspecified '()
;; The actual value of the signal being imposed by the
;; source can be set using the interface of the object
;; which is the returned value of the source constructor.
;;
;; (define s (source wire))
;;
;; (s #t)   ; the signal of the source s is set to #t
;; (s #f)   ; the signal of the source s is set to #f
;; (s '())  ; the signal of the source s is set to '()
;;
;; When a source is connected to a wire, its signal is imposed
;; to the wire: This is implemented by adding an action to the
;; wire's actions list (those actions which are executed following
;; a change of state of the wire). The action being added to the
;; wire's actions list simply re-instate the signal of the source.

(define source    ;; builds a source object connected to 'wire'
  ;;
  ;; static private data
  (let ((time-delay 1)
        ;;
        (init-tag
          (lambda(wire)
            (string->symbol
              (string-append
                "src-"
                (symbol->string (wire 'get-tag)))))))
  ;;
  (lambda (wire)
  ;;
  ;; private data
  (define signal '())
  (define tag '())
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m #t) (set! signal #t)(restore-signal))
          ((eq? m #f) (set! signal #f)(restore-signal))
          ((eq? m '()) (set! signal '())(restore-signal))
          ((eq? m 'get-tag) tag)
          ((eq? m 'signal) signal)
          (else (display "source: unkown operation error\n"))))
  ;;
  ;;
  ;; action added to the wire actions list
  (define (restore-signal)
      (let ((action
              (lambda() ((wire 'set-signal!) signal dispatch))))
        ((global 'add-event!) time-delay action)))
  ;;
  ;; adding new action and initialize tag
  ((wire 'add-action!) restore-signal)
  (set! tag (init-tag wire))
  ;;
  ;; returning interface so source can be toggled between #f, #t and '()
  dispatch)))


