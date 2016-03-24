#!/usr/bin/scm
(load "eval.scm")
(define filename (caddr (program-arguments)))
(load-file filename)
(exit 0)

