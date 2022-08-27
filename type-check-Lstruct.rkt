#lang racket
(require "utilities.rkt")
(require "type-check-Lfun.rkt")
(provide type-check-Lstruct type-check-Lstruct-class)


(define type-check-Lstruct-class
  (class type-check-Lfun-class
	(super-new)
	(inherit check-type-equal? type-check-apply)

	(define-values (struct-ctors getter-idx setter-idx) (values (make-hasheq) (make-hasheq) (make-hasheq)))

	#;(define/override (type-equal? t1 t2)
	  (match* (t1 t2)
		[(`(Vector ,ts) (and st (? symbol?))) 
		 #:when (andmap (lambda (x y) (send this type-equal? x y)) ts (dict-ref struct-ctors st #f))
		#t]
		[((and st (? symbol?)) `(Vector ,ts)) 
		 #:when (andmap (lambda (x y) (send this type-equal? x y)) ts (dict-ref struct-ctors st #f))
		#t]
		[(other wise) (super type-equal? t1 t2)]))

	(define/override ((type-check-exp env) e)
	  (let ([recur (type-check-exp env)])
		(match e
		  [(Apply (Var f) args)
		   #:when (hash-has-key? struct-ctors f)
		   (let-values ([(f^ args^ t) (type-check-apply env (Var f) args)])
			 (values (HasType (Apply f^ args^) `(Vector ,@(dict-ref struct-ctors f)))
					 t))]
		  [else ((super type-check-exp env) e)])))

	(define/override ((new-env-from-def) def env)
	  (match def
		[(StructDef name `([,fs : ,fts] ...))
		 (hash-set! struct-ctors name fts) ;;remember all struct defs
		 (let* ([ctor (cons name `(,@fts -> ,name))])
		   (for/fold ([acc  (cons ctor env)]) 
			 ([f fs] 
			  [ft fts]
			  [i (in-naturals)])
			 (let ([getter-name (string->symbol (format "~a-~a" name f))]
				   [getter-type `(,name -> ,ft)]
				   [setter-name (string->symbol (format "set-~a-~a!" name f))]
				   [setter-type `(,name -> Void)])
			   ;;!! remember getter/setter field index
			   (hash-set! getter-idx getter-name i)
			   (hash-set! setter-idx setter-name i)
			   (append (list (cons getter-name getter-type)
							 (cons setter-type setter-type))
					   acc))))]
		[else ((super new-env-from-def) def env)]
		))
		 
	(define/override ((type-check-def env) e ds^)
	  (match e
		[(? StructDef?) ds^]
		[else ((super type-check-def env) e ds^)]))

	(define/override (type-check-program e)
	  (let ([checked (super type-check-program e)]
			[append-info 
			  (lambda (info)
						   (append `((struct-fields . ,(lambda (name) (dict-ref struct-ctors name #f)))
									 (sturct-getter-idx . ,(lambda (getter) (dict-ref getter-idx getter -1)))
									 (struct-setter-idx . ,(lambda (setter) (dict-ref setter-idx setter -1))))
								   info))])
	    (match checked
	 	 [(ProgramDefsExp info ds body) (ProgramDefsExp (append-info info) ds body)]
	 	 [(ProgramDefs info ds) (ProgramDefs (append-info info) ds)])))

	))



(define (type-check-Lstruct p)
  (send (new type-check-Lstruct-class) type-check-program p))
