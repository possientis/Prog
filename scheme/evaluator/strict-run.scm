#!/usr/bin/scm

(load "main.scm")

(define filename (caddr (program-arguments)))

(strict-load filename)

(exit 0)

