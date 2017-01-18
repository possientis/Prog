#!/usr/bin/scm

(load "main.scm")

(define filename (caddr (program-arguments)))

(analyze-load filename)

(exit 0)

