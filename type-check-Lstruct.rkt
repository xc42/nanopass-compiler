#lang racket
(require "utilities.rkt")
(require "type-check-Lfun.rkt")
(provide type-check-Lstruct type-check-Lstruct-class append-struct-info)

(define append-struct-info (make-parameter #f))

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
		   (let-values ([(f^ args^ t) (type-check-apply env (Var f) args)])
			 (let ([e^ (cond
						 [(hash-ref struct-ctors f #f) => (lambda (v) (StructCtor f args^))]
						 [(hash-ref getter-idx f #f) => (lambda (v) (apply StructGetter (append v args^)))]
						 [(hash-ref setter-idx f #f) => (lambda (v) (apply StructSetter (append v args^)))]
						 [else (Apply f^ args^)])])

			   (values e^ t)))]
		  [(HasType (and st (StructCtor f args)) t) ;;t has Vector type, while StructCtor expr itself has struct type
		   ((type-check-exp env) st)]
		  [(StructCtor f args) 
		   (let-values ([(args^ ts^) (for/lists (args^ ts^) ([arg args]) (recur arg))]
						[(_ ft) (recur (Var f))])
			 (match ft
			   [`(,ts ... -> ,rt)
				 (for-each (lambda (at pt) (check-type-equal? at pt e)) ts^ ts)
				 (values (HasType (StructCtor f args^) `(Vector ,@ts^)) f)]))]
		  [(StructGetter name field idx stct)
		   (let ([f (string->symbol (format "~a-~a" name field))])
			 (let-values ([(f^ args^ t) (type-check-apply env (Var f) (list stct))])
			   (values (StructGetter name field  idx (car args^)) t)))]
		  [(StructSetter name field idx stct e0)
		   (let ([f (string->symbol (format "set-~a-~a!" name field))])
			 (let-values ([(f^ args^ t) (type-check-apply env (Var f) (list stct e0))])
			   (values (StructSetter name field idx (first args^) (last args^)) t)))]

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
				   [setter-type `(,name ,ft -> Void)])
			   (hash-set! getter-idx getter-name (list name f i))
			   (hash-set! setter-idx setter-name (list name f i))
			   (append (list (cons getter-name getter-type)
							 (cons setter-name setter-type))
					   acc))))]
		[else ((super new-env-from-def) def env)]
		))
		 
	(define/override ((type-check-def env) e ds^)
	  (match e
		[(? StructDef?) (cons e ds^)]
		[else ((super type-check-def env) e ds^)]))

	(define/override (type-check-program e)
	  (let ([checked (super type-check-program e)]
			[append-info 
			  (lambda (info)
				(if (append-struct-info)
				  (append `((struct-fields . ,(lambda (name) (dict-ref struct-ctors name #f)))
							(sturct-getter-idx . ,(lambda (getter) (dict-ref getter-idx getter #f)))
							(struct-setter-idx . ,(lambda (setter) (dict-ref setter-idx setter #f))))
						  info)
				  info)
				)])
	    (match checked
	 	 [(ProgramDefsExp info ds body) (ProgramDefsExp (append-info info) ds body)]
	 	 [(ProgramDefs info ds) (ProgramDefs (append-info info) ds)])))

	))



(define (type-check-Lstruct p)
  (send (new type-check-Lstruct-class) type-check-program p))
