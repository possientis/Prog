;;; Scheme chat server
;;; This program implements a simple ‘chat’ server which accepts
;;; connections from multiple clients, and sends to all clients any
;;; characters received from any client.
;;; To connect to chat ‘telnet localhost 8001’

(require 'socket)
(require 'i/o-extensions)

(let ((listener-socket (socket:bind (make-stream-socket af_inet) 8001))
      (connections '()))
  (socket:listen listener-socket 5)
  (do () (#f)
    (let ((actives (or (apply wait-for-input 5 listener-socket connections)
                       '())))
      (cond ((null? actives))
            ((memq listener-socket actives)
             (set! actives (cdr (memq listener-socket actives)))
             (let ((con (socket:accept listener-socket)))
               (display "accepting connection from ")
               (display (getpeername con))
               (newline)
               (set! connections (cons con connections))
               (display "connected" con)
               (newline con))))
      (set! connections
        (let next ((con-list connections))
          (cond ((null? con-list) '())
                (else
                  (let ((con (car con-list)))
                    (cond ((memq con actives)
                           (let ((c (read-char con)))
                             (cond ((eof-object? c)
                                    (display "closing connection from ")
                                    (display (getpeername con))
                                    (newline)
                                    (close-port con)
                                    (next (cdr con-list)))
                                   (else
                                     (for-each (lambda (con)
                                                 (file-position con 0)
                                                 (write-char c con)
                                                 (file-position con 0))
                                               connections)
                                     (cons con (next (cdr con-list)))))))
                          (else (cons con (next (cdr con-list)))))))))))))

