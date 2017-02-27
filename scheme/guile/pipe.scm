; example of guile module usage

(use-modules (ice-9 popen))
(use-modules (ice-9 rdelim))
(define p (open-input-pipe "ls -l"))
(display  (read-line p))(newline)
(display  (read-line p))(newline)
(display  (read-line p))(newline)
(display  (read-line p))(newline)
(display  (read-line p))(newline)
(display  (read-line p))(newline)
(display  (read-line p))(newline)
(display  (read-line p))(newline)



