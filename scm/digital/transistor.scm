(load "wire.scm")

;; This connects three wires called 'gate' 'source' and 'drain'
;; to a MOS transistor of given 'type' (#f or #t).
;;
;; When type = #t the transistor is an n-type transistor
;; This means that the gate wire needs to be in state #t in order
;; for the connection between source and drain to be established.
;;
;; When type = #f the transistor is a p-type transistor
;; This means that the gate wire needs to be in state #f in order
;; for the connection between source and drain to be established.
;;
;; When three wires are connected to a transistor, their respective
;; states are subject to constraints which need to be met. This is
;; implemented by adding three actions (one action for each wire)
;; on the wires' actions list (those actions which are executed
;; following a change of state in a wire). The three actions
;; are described as follows:
;;
;; drain-action:
;; This is the action to be added to the drain's actions list
;; This action will be executed on a drain change of state
;; This action reads the current state of the gate wire,
;; and provided it has the right value (depending on type)
;; it communicates the new drain signal to the source wire
;; as if both wires were connected.
;;
;; source-action:
;; This is the action to be added to the source's actions list
;; This action will be executed on a source change of state
;; This action reads the current state of the gate wire,
;; and provided it has the right value (depending on type)
;; it communicates the new source signal to the drain wire
;; as if both wires were connected.
;;
;; gate-action:
;; This is the action to be added to the gate's actions list
;; This action will be executed on a gate change of state
;; This action reads the new gate signal. The effect of the
;; new gate signal is either the establishment of a connection
;; between drain and source, or the removal of such connection.
;; In the first case, this action will communicate the drain
;; signal to the source and the source signal to the drain.
;; In the second case, this action will notify both the drain
;; and source wires that the transistor relinquishes any claim
;; to impose the current value of their states.

(define transistor  ;; makes a transitor object, duly connected to wires
  ;; type = #t for an n-type transistor
  ;; type = #f for a  p-type transistor
  ;;
  ;; static private data
  (let ((time-fast 1) ; time for propagation of cancel actions
        (time-slow 3) ; time for propagation of ownership actions
        ;;
        ;; static private members
        (init-tag
          (lambda (gate source drain type)
            (let ((str (if (eq? type #t) "n" "p")))
              (string->symbol
                (string-append
                  str
                  "-tr-"
                  (symbol->string (gate 'get-tag))
                  "-"
                  (symbol->string (source 'get-tag))
                  "-"
                  (symbol->string (drain 'get-tag))))))))
  ;;
  (lambda (gate source drain type)
  ;;
  ;; private data
  (define tag '())
  ;;
  ;; public interface
  (define (dispatch m)
    (cond ((eq? m 'get-tag) tag)
          (else (display "transistor: unknown operation error\n"))))
  ;;
  ;; private members
  ;;
  ;; new action to be carried out by the drain wire on a change of state
  (define (drain-action)
    (if (not (eq? (source 'get-signal) (drain 'get-signal)))
      (if (eq? type (gate 'get-signal))
        (let ((action
                (lambda ()
                  (if (not (eq? (drain 'get-signal) (source 'get-signal)))
                    ((source 'set-signal!) (drain 'get-signal) dispatch)))))
          ((global 'add-event!) time-fast action)))))
  ;;
  ;; new action to be carried out by the source wire on a change of state
  (define (source-action)
    (if (not (eq? (source 'get-signal) (drain 'get-signal)))
      (if (eq? type (gate 'get-signal))
        (let ((action
                (lambda ()
                  (if (not (eq? (drain 'get-signal) (source 'get-signal)))
                    ((drain 'set-signal!) (source 'get-signal) dispatch)))))
          ((global 'add-event!) time-fast action)))))
  ;;
  ;; new action to be carried out by the gate wire on a change of state

  (define (gate-action)
    (if (eq? type (gate 'get-signal))
      (begin
       (if (not (eq? (drain 'get-signal) (source 'get-signal)))
         (let ((action
                 (lambda()
                   (if (not (eq? (drain 'get-signal) (source 'get-signal)))
                     (begin
                      ((drain 'set-signal!) (source 'get-signal) dispatch)
                      ((source 'set-signal!) (drain 'get-signal) dispatch))))))
           ((global 'add-event!) time-slow action))))
      (begin
        (let ((action
               (lambda()
                 (if (not (eq? '() (drain 'get-signal)))
                  ((drain 'set-signal!) '() dispatch))
                 (if (not (eq? '() (source 'get-signal)))
                  ((source 'set-signal!) '() dispatch)))))
          ((global 'add-event!) time-fast action)))))

;  (define (gate-action)
;    (let ((action
;            (lambda ()
;              (if (eq? type (gate 'get-signal))
;                (begin
;                  ((drain 'set-signal!) (source 'get-signal) dispatch)
;                  ((source 'set-signal!)(drain 'get-signal) dispatch))
;                (begin
;                  ((drain 'set-signal!) '() dispatch)
;                  ((source 'set-signal!) '() dispatch)))))
;          (time-delay (if (eq? type (gate 'get-signal)) time-slow time-fast)))
;      ((global 'add-event!) time-delay action)))

  ;; initialize tag and adding new actions to respective wires
  (set! tag (init-tag gate source drain type))
  ((gate 'add-action!) gate-action)
  ((source 'add-action!) source-action)
  ((drain 'add-action!) drain-action)
  ;;
  ;; returning public message passing interface
  dispatch)))

(define (n-transistor gate source drain)
  (transistor gate source drain #t))

(define (p-transistor gate source drain)
  (transistor gate source drain #f))
