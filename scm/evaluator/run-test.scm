#!/usr/bin/scm

(load "main.scm")

(define filename (caddr (program-arguments)))

(define analyzed-exp 
  (let ((code (filename->code filename)))
    (analyze code)))

(analyzed-exp global-env)

(exit 0)

