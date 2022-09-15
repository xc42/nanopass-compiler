#lang racket
(require "utilities.rkt")
(require "type-check-Lstruct.rkt")

(define type-check-Lpattern-class
  (class type-check-Lstruct-class
	(super-new)

	(define/override (check-type-equal? t1 t2 e)
		42) ;TODO

	(define/override ((new-env-from-def) def env)
	  (match def
		[(ADTDef name vars) '()] ;TODO
		))


	))


