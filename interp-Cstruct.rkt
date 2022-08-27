#lang racket
(require "utilities.rkt")
(provide interp-Cstruct-mixin)

(define (interp-Cstruct-mixin super-class)
  (class super-class
	(super-new)
	(inherit interp-exp)

	(define/override (interp-stmt env)
	  (lambda (ast)
		(match ast
		  [(? StructSetter?)
		   ((interp-exp env) ast)
		   env]
		  [else ((super interp-stmt env) ast)])))
	))
