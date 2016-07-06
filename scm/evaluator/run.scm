#!/usr/bin/scm
(load "load-file.scm")
(load "eval.scm")
(load "eval-procedure.scm")
(define filename (caddr (program-arguments)))
(load-file filename)
(exit 0)

