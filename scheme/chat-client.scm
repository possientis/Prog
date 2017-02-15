;;; Scheme chat client
;;; this program connects to socket 8001. It then sends all
;;; characters from current-input-port to the socket and sends all
;;; characters from the socket to current-output-port.


; FAILS TO RUN SUCCESSFULLY


(require 'socket)
(require 'i/o-extensions)

(define con (make-stream-socket af_inet))
(set! con (socket:connect con (inet:string->address "localhost") 8001))

(define (go)
  (define actives (wait-for-input (* 30 60) con (current-input-port)))
  (let ((cs (and actives (memq con actives) (read-char con)))
        (ct (and actives (memq (current-input-port) actives) (read-char))))
    (cond ((or (eof-object? cs) (eof-object? ct)) (close-port con))
          (else (cond (cs (display cs)))
                (cond (ct (file-position con 0)
                          (display ct con)
                          (file-position con 0)))
                (go)))))


(cond (con (display "Connecting to ")
           (display (getpeername con))
           (newline)
           (go))
      (else (display "Server not listening on port 8001")
            (newline)))
