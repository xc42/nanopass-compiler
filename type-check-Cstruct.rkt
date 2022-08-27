#lang racket
(require "utilities.rkt")
(provide type-check-Cstruct-mixin)

(define (type-check-Cstruct-mixin super-class)
  (class super-class
    (super-new)
    (inherit new-env-from-def type-check-def)

	(define/override (free-vars-exp e)
	  (define (recur e) (send this free-vars-exp e))
	  (match e
		[(StructGetter _ _ _ stct) (set (Var-name stct))]
		[(StructSetter _ _ _ stct arg) (set-union (recur stct) (recur arg))]
		[else (super free-vars-exp e)]))

	(define/override ((type-check-exp env) e)
	  (match e
		[(StructGetter name _ idx _) 
		 (match (dict-ref env name)
		   [`(,ts ... -> ,name) (values e (list-ref ts idx))])]
		[(? StructSetter?) (values e 'Void)]
		[else ((super type-check-exp env) e)]
		))

	(define/override (type-check-program p)
	  (match p
	    [(ProgramDefs info ds)
		 (define new-env (foldl (new-env-from-def) '() ds))
		 (define ds^ (for/list ([d ds])
					   (cond 
						 [(Def? d) ((type-check-def new-env) d)]
						 [else d])))
		 (ProgramDefs info ds^)]
	    [else (error 'interp-program "unhandled ~a" p)]
	    ))

	))
