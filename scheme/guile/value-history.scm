; API to the value-history feature

(use-modules (ice-9 history)) ; loaded by repl by default

(display "value-history-enabled?: ")(display (value-history-enabled?))(newline)
(display "disabling value-history ...")(disable-value-history!)(newline)
(display "value-history-enabled?: ")(display (value-history-enabled?))(newline)
(display "enabling value-history ...")(enable-value-history!)(newline)
(display "value-history-enabled?: ")(display (value-history-enabled?))(newline)
(display "clearing value-history ...")(clear-value-history!)(newline)


