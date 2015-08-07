(load "wire.scm")

;; creates device connecting wires a and b
;; not a useful primitive, but used in development stages
;;
(define connect
  ;; static private data and members
  (let ((time-delay 1)
        ;;
        (init-tag
          (lambda (a b)
            (string->symbol
              (string-append
                "con-"
                (symbol->string (a 'get-tag))
                "-"
                (symbol->string (b 'get-tag)))))))
  ;;
  (lambda (a b)
  ;;
  ;; data
  (define tag '())      ; used for debugging purposes
  ;;
  ;; interface
  (define (dispatch m)
    (cond ((eq? m 'get-tag) tag)
          (else (display "connect: unknown operation error\n"))))
  ;;
 ;;
  ;; new action to be carried out by wire a on a change of state
  (define (a-action)
    (let ((action
            (lambda () ((b 'set-signal!)(a 'get-signal) dispatch))))
      ((global 'add-event!) time-delay action)))
  ;;
  ;; new action to be carried out by wire b on a change of state
  (define (b-action)
    (let ((action
            (lambda () ((a 'set-signal!)(b 'get-signal) dispatch))))
      ((global 'add-event!) time-delay action)))
  ;;
  ;; initialize tag and adding new actions to respective wires
  (set! tag (init-tag a b))
  ((a 'add-action!) a-action)
  ((b 'add-action!) b-action)

  ;; returning public message passing interface
  dispatch)))
