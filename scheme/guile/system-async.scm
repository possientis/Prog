(display "setting asynchronous call to thunk...\n")
; asynchronous but running immediately it seems
(system-async-mark (lambda() (display "thunk is running\n")))
(display "thunk set up complete...\n")

;;; setting up of async call is done while asyncs are blocked
;;; which means async call does not run before second 'display'
;;; is completed.

;;; not that we do not provide any thread argument (only a proc
;;; arguments. This means the async call will be run by the
;;; same thread as the one calling 'system-async-mark'

(call-with-blocked-asyncs
  (lambda ()
    (display "setting up thunk once more...\n")
    (system-async-mark (lambda () (display "thunk is running again\n")))
    (display "second thunk set up complete...\n")))








