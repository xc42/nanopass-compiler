#lang racket
(require "utilities.rkt")
(require "interp-Lfun.rkt")
(provide interp-Lstruct-class interp-Lstruct)

(define interp-Lstruct-class
  (class interp-Lfun-class
	(super-new)

	(define/override ((interp-exp env) e)
	  (let ([recur (interp-exp env)])
		(match e
		  [(StructCtor _ es) (apply vector (map recur es))]
		  [(StructGetter _ _ idx stct) (vector-ref (recur stct) idx)]
		  [(StructSetter _ _ idx stct e) (vector-set! (recur stct) idx (recur e))]
		  [else ((super interp-exp env) e)])))
	))

(define (interp-Lstruct p)
  (send (new interp-Lstruct-class) interp-program p))
