#lang racket
(require "utilities.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Cfun.rkt")
;(require "type-check-Cany.rkt")
(require "type-check-Cwhile.rkt")
(require "type-check-Lvecof.rkt")
(provide type-check-Cvecof type-check-Cvecof-mixin type-check-Cvecof-class)

(define (type-check-Cvecof-mixin super-class)
  (class super-class
    (super-new)
	(inherit check-type-equal?)

    (define/override (free-vars-exp e)
      (define (recur e) (send this free-vars-exp e))
      (match e
        [(AllocateHom e-len e-amount ty) (set-union (recur e-len) (recur e-amount))]
	[else (super free-vars-exp e)]))

    (define/override (type-check-exp env)
      (lambda (e)
        (debug 'type-check-exp "Lvecof" e)
        (define recur (type-check-exp env))
        (match e
          [(Prim 'make-vector (list e1 e2))
           (define-values (e1^ t1) (recur e1))
           (define-values (e2^ elt-type) (recur e2))
           (define vec-type `(Vectorof ,elt-type))
           (values (HasType (Prim 'make-vector (list e1^ e2^)) vec-type)
                   vec-type)]
          [(HasType (Prim 'make-vector es) t)
           (recur (Prim 'make-vector es))]

          [(Prim (or 'vector-ref 'vectorof-ref) (list e1 e2))
           (define-values (e1^ t1) (recur e1))
           (define-values (e2^ t2) (recur e2))
           (match* (t1 t2)
             [(`(Vectorof ,elt-type) 'Integer)
              (values (Prim 'vectorof-ref (list e1^ e2^)) elt-type)]
             [(other wise) ((super type-check-exp env) e)])]
          [(Prim (or 'vector-set! 'vectorof-set!) (list e1 e2 e3) )
           (define-values (e-vec t-vec) (recur e1))
           (define-values (e2^ t2) (recur e2))
           (define-values (e-arg^ t-arg) (recur e3))
           (match t-vec
             [`(Vectorof ,elt-type)
              (check-type-equal? elt-type t-arg e)
              (values (Prim 'vectorof-set! (list e-vec e2^ e-arg^))  'Void)]
             [else ((super type-check-exp env) e)])]
          [(Prim (or 'vector-length 'vectorof-length) (list e1))
           (define-values (e1^ t1) (recur e1))
           (match t1
             [`(Vectorof ,t)
              (values (Prim 'vectorof-length (list e1^))  'Integer)]
             [else ((super type-check-exp env) e)])]

          [(AllocateHom e1 e2 t)
           (define-values (e1^ t1) (recur e1))
           (define-values (e2^ t2) (recur e2))
           (check-type-equal? t1 'Integer e)
           (check-type-equal? t2 'Integer e)
           (values (AllocateHom e1^ e2^ t) t)]
          
          [else ((super type-check-exp env) e)])))

    ))

(define type-check-Cvecof-class
  (type-check-Cvecof-mixin
	;(type-check-Cany-mixin
	;(type-check-Cfun-mixin
	(type-check-Cvec-mixin
	  (type-check-Cwhile-mixin
		(type-check-Cif-mixin
		  (type-check-Cvar-mixin
			type-check-Lvecof-class))))))

(define (type-check-Cvecof p)
  (send (new type-check-Cvecof-class) type-check-program p))

        
