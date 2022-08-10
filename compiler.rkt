#lang racket
(require racket/set racket/stream racket/promise)
(require data/queue)
(require graph)
(require "utilities.rkt")
(require "type-check-Clambda.rkt")
(require "type-check-Llambda.rkt")
(require (prefix-in runtime-config:: "runtime-config.rkt"))

(provide (all-defined-out))


(define-syntax-rule (map-program-def f p)
  (match-let ([(ProgramDefs info defs) p])
			 (ProgramDefs info (map f defs))))

(define-syntax-rule (map-program-def-body f p)
  (map-program-def (lambda (def) 
					 (match-let ([(Def fn ps rt info body) def])
								(Def fn ps rt info (f body))))
				   p))

(define (fn-start-label fn) (string->symbol (~a fn 'start)))

;;apply f to expr recursively
(define (fmap-expr f expr)
	(match expr
		   [(Prim op es) (Prim op (map f es))]
		   [(If e1 e2 e3) (If (f e1) (f e2) (f e3))]
		   [(Apply func args) (Apply (f func) (map f args))]
		   [(Let v e body) (Let v (f e) (f body))]
		   [(Lambda ps rt body) (Lambda ps rt (f body))]
		   [(HasType e t) (HasType (f e) t)]
		   [(SetBang v e) (SetBang v (f e))]
		   [(Begin es e) (Begin (map f es) (f e))]
		   [(WhileLoop cnd body) (WhileLoop (f cnd) (f body))]
		   [else expr]))

(define (shrink p)
  (define (shrink-exp e)
	(match e
	  [(Prim op `(,e1 ,es ...))
	   (let* ([e1 (shrink-exp e1)]
			  [es (map shrink-exp es)]
			  [new-es (cons e1 es)]
			  [T (Bool #t)]
			  [F (Bool #f)])
		 (match op
		   ['- (if (eq? es '()) 
				 (Prim op `(,e1))
				 (Prim '+ `(,e1 ,(Prim '- es))))]
		   ['and (If e1 (If (car es) T F) F)]
		   ['or (If e1 T (If (car es) T F))]
		   ;['<= (If (Prim '< new-es) T (If (Prim 'eq? new-es) T F))]
		   ;['>= (Prim 'not `(,(Prim '< new-es)))]
		   ;['>  (If (Prim 'not `(,(Prim '< new-es))) (If (Prim 'eq? new-es) F T) F)]
		   [other (Prim op new-es)]))]
	  [else (fmap-expr shrink-exp e)]))
  (match p
	[(Program info body)
	 (ProgramDefs info `(,(Def 'main '() 'Integer '() (shrink-exp body))))]
	[(ProgramDefsExp info defs expr) 
	 (ProgramDefs info (append
						 (for/list ([def (in-list defs)])
						   (match-let ([(Def fn ps rt info body) def])
							 (Def fn ps rt info (shrink-exp body))))
						 `(,(Def 'main '() 'Integer '() (shrink-exp expr)))))]))


(define (uniquify p)
  (define (uniquify-exp env)
	(lambda (expr)
	  (let ([uniq (uniquify-exp env)])
		(match expr
		  [(Var x) (Var (lookup x env))]
		  [(SetBang x e) (SetBang (lookup x env) (uniq e))]
		  [(Let x e body)
		   (let ([x* (gensym x)])
			 (Let x* (uniq e) ((uniquify-exp (extend-env env x x*)) body)))]
		  [(Lambda `([,xs : ,ts] ...) rt body) 
		   (let* ([xs^ (map gensym xs)]
				  [ps^ (map (lambda (x t) `(,x : ,t)) xs^ ts)]
				  [env-ex (for/fold ([env^ env])
							([x xs] 
							 [x^ xs^])
							(extend-env env^ x x^))])
			 (Lambda ps^ rt ((uniquify-exp env-ex) body)))]
		  [else (fmap-expr uniq expr)]))))
  (match p
	[(Program info body) (Program info ((uniquify-exp '()) body))]
	[(ProgramDefs info defs)
	 (let ([global-env (foldl (lambda (def env) (extend-env env (Def-name def) (Def-name def))) '() defs)])
	   (ProgramDefs info 
					(for/list ([def (in-list defs)])
					  (match-let ([(Def fn ps rt info body) def])
						(let ([init-env 
								(foldl 
								  (lambda (param env) 
									(let ([var (if (pair? param) (car param) param)])
									  (extend-env env var var))) 
								  global-env 
								  ps)])
						  (Def fn ps rt info ((uniquify-exp init-env) body)))))))])) 


(define (reveal-functions p)
  (let ([fs (for/list ([def (ProgramDefs-def* p)]) 
					(cons (Def-name def) (length (Def-param* def))))])
	(letrec ([reveal-functions*
			   (lambda (expr)
				 (match expr
						[(Var v) (let ([f* (assv v fs)]) (if  f* (FunRef v (cdr f*)) expr))]
						[else (fmap-expr reveal-functions* expr)]))])
	  (match p
			 [(? Program?) p]
			 [(? ProgramDefs?) (map-program-def-body reveal-functions* p)]))))

(define (free-variable expr)
  (match expr
	[(? Var?) (set expr)]
	[(? HasType?) (if (Var? (HasType-expr expr))
					(set expr) ;;to keep var's type info, used in closure conversion pass
					(free-variable (HasType-expr expr)))]
	[(Let x e body) (set-union (free-variable e) (set-remove (free-variable body) (Var x)))]
	[(Lambda ps rty body) (set-subtract (free-variable body) 
										(for/set ([p ps]) (HasType (Var (car p)) (last p))))]
	[(If e1 e2 e3) (apply set-union (map free-variable `(,e1 ,e3 ,e3)))]
	[(Apply f args) (apply set-union (map free-variable (cons f args)))]
	[(Prim op es) (apply set-union (map free-variable es))]
	[(SetBang v e) (set-add (free-variable e) (Var v))]
	[(Begin es body) (apply set-union (cons (free-variable body) (map free-variable es)))]
	[(WhileLoop cnd body) (set-union (free-variable cnd) (free-variable body))]
	[else (set)]))


(define (convert-assignment p)

  (define (gather-assigned-free expr)
	(match expr
	  [(SetBang v e)
	   (let-values ([(e^ A F) (gather-assigned-free e)]) ;; A: assigned F:free-variable
		 (values (SetBang v e^) (set-add A v) F))]
	  [(Lambda ps rt body)
	   (let-values ([(body^ A F) (gather-assigned-free body)]
					[(xs) (for/set ([xt ps]) (car xt))]
					[(fvs) (for/set ([fv (free-variable body)]) (Var-name fv))])
		 (values (Lambda ps rt body^) (set-subtract A xs) (set-subtract (set-union F fvs) xs)))]
	  [(Let v e body) 
	   (let-values ([(e^ Ae Fe)  (gather-assigned-free e)]
					[(body^ Ab Fb) (gather-assigned-free body)])
		 (let ([v^ (if (and (set-member? Ab v) (set-member? Fb v))
					 (AssignedFree v)
					 v)])
		   (values (Let v^ e^ body^) (set-union Ae Ab) (set-union Fe Fb))))]
	  [(Prim op es) (gather-es es (lambda (es^) (Prim op es^)))]
	  [(If pred thn els) (gather-es `(,pred ,thn ,els) (lambda (es^) (apply If es^)))]
	  [(Apply f args) (gather-es (cons f args) (lambda (es^) (Apply (car es^) (cdr es^))))]
	  [(Begin es* body) (gather-es (cons body es*) (lambda (es^) (Begin (cdr es^) (car es^))))]
	  [(WhileLoop cnd body) (gather-es `(,cnd ,body) (lambda (es^) (apply WhileLoop es^)))]
	  [(HasType e t) (gather-es `(,e) (lambda (es^) (HasType (car es^) t)))]
	  [_ (values expr (set) (set))]))

  (define (gather-es es ctor)
	(for/foldr ([acc-e '()] 
				[A (set)] 
				[F (set)]
				#:result (values (ctor acc-e) A F))
	  ([e es])
	  (let-values ([(e^ a f) (gather-assigned-free e)])
		(values (cons e^ acc-e) (set-union a A) (set-union f F)))))
	  

  (define (convert-def def)
	(match-let ([(Def name ps rt info body) def])
	  (let-values ([(body^ A F) (gather-assigned-free body)])

		(define (assign&free v)
		  (and (set-member? A v) (set-member? F v)))

		(define (convert-expr expr)
		  (match expr
			[(Var x) 
			 (cond
			   [(set-member? A x) (if (set-member? F x) 
									(Prim 'vector-ref `(,(Var x) ,(Int 0))) 
									(GetBang x))]
			   [else expr])]
			[(Let (AssignedFree x) e body) (Let x (Prim 'vector `(,(convert-expr e))) (convert-expr body))]
			[(SetBang v e) 
			 (if (assign&free v)
			   (Prim 'vector-set! `(,(Var v) ,(Int 0) ,(convert-expr e)))
			   (SetBang v (convert-expr e)))]
			[(Lambda ps rt body) 
			 (let-values ([(ps^ body^) (convert-fun ps (convert-expr body))])
			   (Lambda ps^ rt body^))]
			[else (fmap-expr convert-expr expr)]))

		(define (convert-fun ps body)
		  (for/foldr ([xs^ '()]
					  [body^ body])
					 ([xt ps])
					 (let ([x (car xt)])
					   (cond
						 [(assign&free x)
						  (let ([x^ (gensym x)])
							(values (cons (cons x^ (cdr xt)) xs^)
									(Let x (Prim 'vector `(,(Var x^))) body^)))]
						 [else (values (cons xt xs^) body^)]))))

		(let-values ([(ps^ body^^) (convert-fun ps (convert-expr body^))])
		  (Def name ps^ rt info body^^)))))

  (map-program-def convert-def p))
						

(define (convert-to-closure p)

  ;;wrap type info of applied function for later use (limit-functions  for overflowd args)
;  (define check-apply-type-class
;	(class type-check-Llambda-class
;	  (super-new)
;	  (inherit type-check-exp)
;	  (inherit check-type-equal?)
;	  (define/override (type-check-apply env e es)
;		(define-values (e^ ty) ((type-check-exp env) e))
;		(define-values (e* ty*) (for/lists (e* ty*) ([e (in-list es)])
;										   ((type-check-exp env) e)))
;		(match ty
;		  [`(,ty^* ... -> ,rt)
;			(for ([arg-ty ty*] [param-ty ty^*])
;			  (check-type-equal? arg-ty param-ty (Apply e es)))
;			(values (HasType e^ ty) e* rt)]
;		  [else (error 'type-check "expected a function, not ~a" ty)]))))


  (define (convert-func-type rt)
	(match rt
	  [`(,ps ... -> ,rt*) `(Vector ((Vector _) ,@(map convert-func-type ps) -> ,rt*))] ;;convert function type to closure type
	  [`(Vector ,ts ...) `(Vector ,@(map convert-func-type ts))]
	  [else rt]))

  (define (convert-param-func-type ps)
	(match ps
	  [`([,xs : ,ts] ...) (for/list ([x xs] [t ts]) `(,x : ,(convert-func-type t)))]))
		
  (define (convert-def def)
	(let* ([lam-prefix (string->symbol (~a (Def-name def) "_lambda"))]
		   [lift-fns '()]
		   [add-lift-fn (lambda (def)
						  (set! lift-fns (cons def lift-fns)))])


	  (define (convert-expr expr)
		(match expr
		  [(Lambda ps rt body) 
		   (let* ([lift-fn-name (gensym lam-prefix)]
				  [arity (length ps)]
				  [fvs 
					(for/list ([fv (free-variable expr)])
					  (HasType (HasType-expr fv) (convert-func-type (HasType-type fv))))]
				  [clos-param (Var (gensym 'clos))]
				  [clos-type `(Vector _ ,@(map HasType-type fvs))]
				  [body^ 
					(let let-header ([fvs* fvs] [idx 1])
					  (if (null? fvs*)
						(convert-expr body)
						(Let (Var-name (HasType-expr (car fvs*))) 
							 (Prim 'vector-ref `(,clos-param ,(Int idx)))
							 (let-header (cdr fvs*) (+ 1 idx)))))]
				  [lift-fn 
					(Def lift-fn-name 
						 (cons `(,(Var-name clos-param) : ,clos-type) (convert-param-func-type ps))
						 (convert-func-type rt) 
						 '() 
						 body^)])

			 (add-lift-fn lift-fn)
			 (Closure arity (cons (FunRef lift-fn-name arity) fvs)))]

		  [(Apply f-expr args)
		   (let ([tmp (gensym 'clos_tmp)])
			 (Let  tmp (convert-expr f-expr)
				   (Apply (Prim 'vector-ref `(,(Var tmp),(Int 0)))
						  (cons (Var tmp) (map convert-expr args)))))]

		  [(FunRef name arity) (Closure arity (list (FunRef name arity)))]
		  [else (fmap-expr convert-expr expr)]))

	  (match-let ([(Def name ps rt info body) def])
		(let ([ps^ (convert-param-func-type
						(if (eq? name 'main)
						  ps
						  (cons '(dummy_clos : (Vector _)) ps)))]
			  [rt^ (convert-func-type rt)]
			  [body^ (convert-expr body)])
		  (cons (Def name ps^ rt^ info body^) lift-fns)))))

  (let* ([type-check
		   (lambda (p)
			 (parameterize ([typed-vars #t]) 
			   (send (new type-check-Llambda-class) type-check-program p)))]
		 [p^ (type-check p)])
	(type-check ;;type-check again to "correct" type inconsistency of closure type(aka. vector) and function
	  (ProgramDefs (ProgramDefs-info p^)
				   (foldr (lambda (def acc) (append (convert-def def) acc))
						  '()
						  (ProgramDefs-def* p^))))))

  
; R5 -> R5
(define (limit-functions p)
  (define arg-limit (vector-length arg-registers))

  ;to pack overflowed args to vector need to know their type
  (define expose-apply-type-class
	(class type-check-Llambda-class
		   (super-new)
		   (inherit type-check-exp)
		   (inherit check-type-equal?)
		   (define/override (type-check-apply env e es)
						  (let-values ([(e^ ty) ((type-check-exp env) e)]
									   [(e* ty*) (for/lists (e* ty*) ([e (in-list es)])
															((type-check-exp env) e))])
							(match ty
								   [`(,ty^* ... -> ,rt) 
									 (for ([arg-ty ty*] [param-ty ty^*])
									   (check-type-equal? arg-ty param-ty (Apply e es)))
									 (let ([args^ (for/list ([e e*] [ty ty*])
												   (if (HasType? e) e (HasType e ty)))])
									   (values e^ args^ rt))]
								   [else (error 'type-check "expected a function, not ~a" ty)])))))
		  
  (define (limit-def def)

	(define (limit-apply expr)
	  (match expr
		[(Apply f args)
		 (let ([f^ (limit-apply f)]
			   [args^ (map limit-apply args)])
		   (if (<= (length args^) arg-limit)
			 (Apply f^ args^)
			 (let* ([head (take args^ (- arg-limit 1))]
					[tail (drop args^ (- arg-limit 1))]
					[vec-arg (HasType (Prim 'vector tail) `(Vector ,@(map HasType-type tail)))]);;wrap vector with HasType for expose-allocation pass
			   (Apply f^ (append head `(,vec-arg))))))]
		[else (fmap-expr limit-apply expr)])) ;;limit-apply

	(define (limit-def^ ps body)
	  (let* ([head (take ps (- arg-limit 1))]
			 [tail (drop ps (- arg-limit 1))]
			 [vec-param (gensym 'auto-vec-param)]
			 [vec-ts (match tail 
					   [`([,xs : ,ts] ...) `(Vector ,@ts)])]
			 [ps^ (append head `((,vec-param : ,vec-ts)))]
			 [body^
			   (let let-header ([tl tail]  [idx 0])
				 (if (null? tl)
				   (limit-apply body)
				   (Let (caar tl) (Prim 'vector-ref `(,(Var vec-param) ,(Int idx)))
						(let-header (cdr tl) (+ idx 1)))))])
		(values ps^ body^)))


	(match-let ([(Def fn ps rt info body) def])
	  (if (<= (length ps) arg-limit)
		(Def fn ps rt info (limit-apply body))
		(let-values ([(ps^ body^) (limit-def^ ps body)])
		  (Def fn ps^ rt info body^)))))


  (let* ([type-check (lambda (p) 
					  (parameterize ([typed-vars #t]) ;;note: to preserve type info (HasType free var) in Closure
						(send (new expose-apply-type-class) type-check-program p)))]
		[p^ (type-check p)])
	(match p^
		   [(? Program?) p^]
		   [(ProgramDefs info defs) (type-check (ProgramDefs info (map limit-def defs)))])))


(define (expose-allocation p)
  (define (calc-bytes-needed t)
	(match t
	  ['Integer 8]
	  [`(,ps ... -> ,ts) 8] ;;function pointer
	  [`(Vector ,ts ...) (for/fold ([acc 8]) ([t* ts]) (+ acc (calc-bytes-needed t*)))]))

  (define (do-allocate es bytes alloc-expr)
	(let* ([var-vec (gensym 'alloc)]
		   [es^ (let all-assign ([idx 0] [es* es])
				  (if (null? es*)
					'()
					(cons (Prim 'vector-set! `(,(Var var-vec) ,(Int idx) ,(car es*)))
						  (all-assign (+ idx 1) (cdr es*)))))]
		   [assign-body (Let var-vec alloc-expr (Begin es^ (Var var-vec)))])
								  
	  (Begin
		   `(,(If (Prim '< 
					 (list (Prim '+ `(,(GlobalValue 'free_ptr) ,(Int bytes)))
						   (GlobalValue 'fromspace_end)))
			   (Void)
			   (Collect bytes)))
		   assign-body)))


  (define (expose-allocation-expr expr)
	(match expr
	  [(HasType (Prim 'vector es) ts) 
	   (let ([bytes (calc-bytes-needed ts)])
		 (do-allocate (map expose-allocation-expr es) bytes (Allocate bytes ts)))]
	  [(HasType (Closure arity es) ts)
	   (let ([bytes (calc-bytes-needed ts)])
		 (do-allocate (map expose-allocation-expr es) bytes (AllocateClosure bytes ts arity)))]
	  [else (fmap-expr expose-allocation-expr expr)]))

  (define (unwarp-HasType expr)
	(match expr
	  [(HasType e t) (unwarp-HasType e)]
	  [else (fmap-expr unwarp-HasType expr)]))

  (match p
	[(Program info e) (Program info (expose-allocation-expr e))]
	[(? ProgramDefs?) (map-program-def-body (compose unwarp-HasType expose-allocation-expr) p)]))
																				  

			
(define (remove-complex-opera* p)
  (define (nested-let es rand-acc inner-most)
		   (if (null? es)
			   (inner-most rand-acc)
			   (let ([e (car es)])
				 (if (atm? e)
					 (nested-let (cdr es) (cons e rand-acc) inner-most)
					 (let ([v (gensym 'tmp)])
					   (Let v (rco-expr e) (nested-let (cdr es) (cons (Var v) rand-acc) inner-most)))))))

  (define (rco-atm expr)
	(match expr
		[(Prim op es) (nested-let es '() (lambda (acc) (Prim op (reverse acc))))]
		[(Apply f args) 
		 (nested-let (cons f args) '() (lambda (acc) 
										 (let ([r-acc (reverse acc)])
										   (Apply (car r-acc) (cdr r-acc)))))]))

  (define (rco-expr expr)
	(match expr
		[(? Prim?) (rco-atm expr)]
		[(? Apply?) (rco-atm expr)] 
		[else (fmap-expr rco-expr expr)]))

  (match p
		 [(Program info expr) (Program info (rco-expr expr))]
		 [(? ProgramDefs?) (map-program-def-body rco-expr p)]))


(define (explicate-control p)

  (define (explicate-control-expr expr-body start-label)
	(let* ([CFG (list)]
		   [add-CFG
			 (lambda (block [label-str ""])
			   (if (Goto? block)
				 block
				 (let ([label (cond
								[(string? label-str) (if (equal? label-str "") 
													   (gensym 'block) 
													   (string->symbol label-str))]
								[else label-str])])
				   (set! CFG (cons (cons label block) CFG))
				   (Goto label))))]
		   [lz-add-CFG
			 (lambda (block [label-str ""])
			   (delay (add-CFG block label-str)))])

	  (define (explicate-assign var expr acc)
		(match expr
		  [(Let v e body) (explicate-assign v e (explicate-assign var body acc))]
		  [(If pred thn els)
		   (let ([acc-label (add-CFG acc)])
			 (explicate-pred pred  
							 (lz-add-CFG (explicate-assign var thn acc-label))
							 (lz-add-CFG (explicate-assign var els acc-label))))]
		  [(Apply f args) (Seq (Assign (Var var) (Call f args)) acc)]
		  [(SetBang v e) (explicate-assign v e acc)]
		  [(Begin es body) (foldr explicate-effect (explicate-assign var body acc) es)]
		  [(WhileLoop cnd body) (explicate-effect expr (explicate-assign var (Void) acc))]
		  [(GetBang v) (Seq (Assign (Var var) (Var v)) acc)]
		  [other (Seq (Assign (Var var) expr) acc)]))

	  (define (explicate-pred pred lz-thn lz-els)
		(match pred
		  [(Bool #t)  (force lz-thn)]
		  [(Bool #f)  (force lz-els)]
		  [(Var b) (IfStmt (Prim 'eq? `(,pred ,(Bool #t))) (force lz-thn) (force lz-els))]
		  [(GetBang e) (explicate-pred (Var e) lz-thn lz-els)]
		  [(Apply f args) 
		   (let ([v (gensym 'auto-if-call)]) 
			 (explicate-assign v (Call f args) (explicate-pred (Var v) lz-thn lz-els)))]
		  [(Prim (or 'eq? '< '<= '> '>=) rands) (IfStmt pred (force lz-thn) (force lz-els))]
		  [(Prim 'not `(,pred*)) (explicate-pred pred* lz-els lz-thn)]
		  [(Let v e body) (explicate-assign v e (explicate-pred body lz-thn lz-els))]
		  [(Begin es body) (foldr explicate-effect (explicate-pred body lz-thn lz-els) es)]
		  [(If pred* thn* els*) 
		   (explicate-pred pred* 
						   (lz-add-CFG (explicate-pred thn* lz-thn lz-els)) 
						   (lz-add-CFG (explicate-pred els* lz-thn lz-els)))]))

	  (define (explicate-effect expr acc)
		(match expr
		  [(SetBang v e) (explicate-assign v e acc)]
		  [(Begin es body) (foldr explicate-effect (explicate-effect body acc) es)]
		  [(WhileLoop cnd body)
		   (let* ([loop (gensym 'loop)]
				  [block (explicate-pred cnd (lz-add-CFG (explicate-effect body (Goto loop))) (lz-add-CFG acc))])
			 (begin
			   (add-CFG block loop)
			   block))]
		  [(Let v e body) (explicate-assign v e (explicate-effect body acc))]
		  [(If pred thn els)
		   (let ([acc^ (add-CFG acc)])
			 (explicate-pred pred 
							 (lz-add-CFG (explicate-effect thn acc^)) 
							 (lz-add-CFG (explicate-effect els acc^))))]
		  [(or (Prim 'vector-set! _) (Prim 'read '()) (? Collect?)) ;;side effect primitives(see utilities.rkt stmt?)
		   (Seq expr acc)]
		  [(Apply f args) (Seq (Call f args) acc)]
		  [_ acc];;can ommit pure expr
		  ))


	  (define (explicate-tail expr)
		(match expr
		  [(Let var e body) (explicate-assign var e (explicate-tail body))]
		  [(If pred thn els) (explicate-pred pred (lz-add-CFG (explicate-tail thn)) (lz-add-CFG (explicate-tail els)))]
		  [(Apply f args) (TailCall f args)]
		  [(Begin es body) (foldr explicate-effect (explicate-tail body) es)]
		  [(WhileLoop cnd body) (explicate-pred cnd 
												(lz-add-CFG (explicate-effect body (Goto (gensym 'loop))))
												(lz-add-CFG (Return (Void))))]
		  [(SetBang v e) (explicate-assign v e (Return (Void)))]
		  [(GetBang e) (Return (Var e))]
		  [other (Return expr)]))

	  (begin (add-CFG (explicate-tail expr-body) (symbol->string start-label)) 
			 CFG)))

	  (match p
			 ;[(Program info e) (CProgram info (explicate-control-expr e 'start))]
			 [(ProgramDefs info defs) 
			  (ProgramDefs info (for/list ([def (in-list defs)])
										  (match-let ([(Def fn ps rt info body) def])
													 (Def fn ps rt info (explicate-control-expr body (fn-start-label fn))))))]))

       

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (define (constant? e)
	(or (Int? e) (Bool? e)))

  (define (to-X86-val e)
	(match e
	  [(Int n) (Imm n)]
	  [(Bool b) (Imm (if b 1 0))]
	  [else e]))

  (define (get-const-val r2)
	(match r2
	  [(Bool b) b]
	  [(Int n) n]))

  (define (get-vec-tag vec-ts)
	(let ([mask (let pointer-mask ([ts* (cdr vec-ts)])
				  (cond
					[(null? ts*) 0]
					[else (bitwise-ior (arithmetic-shift (pointer-mask (cdr ts*)) 1) 
								 (match (car ts*)
								   [`(Vector ,t ...) 1]
								   [else 0]))]))]
		  [len (length (cdr vec-ts))]
		  [<< arithmetic-shift]
		  [|| bitwise-ior])
	  ((mask . << . 7) . || . ((len . << . 1) . || . 0))))

  (define (push-args args)
	(for/list ([arg args]
			   [r arg-registers])
	  (Instr 'movq (list (to-X86-val arg) (Reg r)))))

  (define (cmpop->flag op)
	(match op
	  ['eq?  (cons equal? 'e)]
	  ['< (cons < 'l)]
	  ['<= (cons <= 'le)]
	  ['> (cons > 'g)]
	  ['>= (cons >= 'ge)]))


  (define (trans-assign dst expr)
	(match expr
	  [(Int n) `(,(Instr 'movq (list (Imm n) dst)))]
	  [(Bool b) `(,(Instr 'movq (list (Imm (if b 1 0)) dst)))]
	  [(Var v) `(,(Instr 'movq (list (Var v) dst)))]
	  [(GlobalValue var) `(,(Instr 'movq (list (Global var) dst)))]
	  [(Void) `(,(Instr 'movq (list (Imm 0) dst)))]
	  [(FunRef f arity) `(,(Instr 'leaq (list (Global f) dst)))]
	  [(Call f args) `(,@(push-args args)
						,(IndirectCallq f (length args))
						,(Instr 'movq (list (Reg 'rax) dst)))]

	  [(Prim 'read '()) `(,(Callq 'read_int 0) ,(Instr 'movq (list (Reg 'rax) dst)))]
	  [(Prim 'not `(,e)) 
	   (match e
		 [(Bool b) `(,(Instr 'movq (list (Imm (if b 0 1)) dst)))]
		 [(Var v)  (if (equal? e dst)
					 `(,(Instr 'xorq (list (Imm 1) dst)))
					 `(,(Instr 'movq (list e dst)) ,(Instr 'xorq (list (Imm 1) dst))))])]
	  [(Prim '- `(,e)) 
	   (if (Int? e)
		 (match-let ([(Int n) e]) `(,(Instr 'movq (list (Imm (- n)) dst))))
		 `(,(Instr 'movq (list e dst)) ,(Instr 'negq (list dst))))]

	  [(Prim (or '+ '- '*) `(,e1 ,e2)) 
	   (let ([instr (match (Prim-op expr)
					  ['+ 'addq]
					  ['- 'subq]
					  ['* 'imulq])])
		 `(,(Instr 'movq `(,(to-X86-val e2) ,dst))
		   ,(Instr instr `(,(to-X86-val e1) ,dst))))]
	  [(Prim 'vector-ref `(,v ,i))
	   (list (Instr 'movq `(,v ,(Reg 'r11)))
			 (Instr 'movq `(,(Deref 'r11 (* 8 (+ (Int-value i) 1))) ,dst)))]
	  [(Prim 'vector-set! `(,v ,i ,arg))
	   (list (Instr 'movq `(,v ,(Reg 'r11)))
			 (Instr 'movq `(,(to-X86-val arg) ,(Deref 'r11 (* 8 (+ (Int-value i) 1)))))
			 (Instr 'movq `(,(Imm 0) ,dst)))]
	  [(Prim (or 'eq? '< '<= '> '>=) `(,e1 ,e2))
	   (match-let ([`(,op . ,cc) (cmpop->flag (Prim-op expr))])
		 (cond 
		   [(and (constant? e1) (constant? e2)) `(,(Instr 'movq (list (Imm (if (op (get-const-val e1) (get-const-val e2)) 1 0)) dst)))]
		   [else `(,(Instr 'cmpq `(,(to-X86-val e2) ,(to-X86-val e1))) 
					,(Instr 'set (list cc (ByteReg 'al))) 
					,(Instr 'movzbq (list (ByteReg 'al) dst)))]))]
	  [(or (Allocate bytes ts) (AllocateClosure bytes ts _))
	   (list (Instr 'movq `(,(Global 'free_ptr) ,(Reg 'r11)))
			 (Instr 'addq `(,(Imm bytes) ,(Global 'free_ptr)))
			 (Instr 'movq `(,(Imm (get-vec-tag ts)) ,(Deref 'r11 0)))
			 (Instr 'movq `(,(Reg 'r11) ,dst)))]
	  [(Collect bytes)
	   (list (Instr 'movq `(,(Reg rootstack-reg) ,(Reg 'rdi)))
			 (Instr 'movq `(,(Imm bytes) ,(Reg 'rsi)))
			 (Callq 'collect 2))]))

  (define (trans-seq stmt)
	(define (trans-effect expr)
	  (match expr
		[(Prim 'read '()) `(,(Callq 'read_int 0))]
		[(Prim 'vector-set! `(,v ,i ,arg))
		 `(,(Instr 'movq `(,v ,(Reg 'r11)))
			,(Instr 'movq `(,(to-X86-val arg) ,(Deref 'r11 (* 8 (+ (Int-value i) 1))))))]
		[(Call f args) `(,@(push-args args)
						  ,(IndirectCallq f (length args)))]
		[(Collect bytes)
		 `(,(Instr 'movq `(,(Reg rootstack-reg) ,(Reg 'rdi)))
			,(Instr 'movq `(,(Imm bytes) ,(Reg 'rsi)))
			,(Callq 'collect 2))]))
	(match stmt
	  [(Assign dst expr) (trans-assign dst expr)]
	  [else (trans-effect stmt)]))


  (define (trans-tail tail)
	(match tail
	  [(Goto label) `(,(Jmp label))]
	  [(Seq s1 tail) (append (trans-seq s1) (trans-tail tail))]
	  [(TailCall f args) `(,@(push-args args)
							,(TailJmp f (length args)))]
	  [(IfStmt pred thn els)
	   (match-let ([(Prim op `(,e1 ,e2))  pred])
		 (let ([v1 (to-X86-val e1)]
			   [v2 (to-X86-val e2)]
			   [flag (cdr (cmpop->flag op))])
		   `(,(Instr 'cmpq (list v2 v1)) ,(JmpIf flag (Goto-label thn)) ,(Jmp (Goto-label els)))))]
	  [(Return expr) (trans-assign (Reg 'rax) expr)]))

  (define (num-root-spills info)
	(count (lambda (ts) (and (pair? ts) (eq? 'Vector (car ts)))) (dict-ref info 'locals-types '())))

  (define (trans-def def)
	(match-let ([(Def fn ps rt info CFG) def])
	  (let ([info^
			  (append 
				(list 
				  (cons 'num-params (length ps))
				  (cons 'name fn)
				  (cons 'num-root-spills (num-root-spills info))) ; for interp-x86-2
				info)]
			[CFG^ 
			  (for/list ([bb CFG])
				(let ([label (car bb)] 
					  [stmts (cdr bb)]
					  [start (fn-start-label fn)]
					  [arg-pass-stmts
						(for/list ([p ps]
								   [r arg-registers])
						  (Instr 'movq `(,(Reg r) ,(Var (car p)))))])
				  (cons label 
						(if (eq? label start)
						  (Block '() (append arg-pass-stmts (trans-tail stmts)))
						  (Block '() (trans-tail stmts))))))])
		(Def fn ps rt info^ CFG^))))

  (match (send (new type-check-Clambda-class) type-check-program p)
	[(ProgramDefs info defs) (ProgramDefs info (map trans-def defs))]))


(define (remove-jumps p)
  (define (occur-once xs)
	(if (null? xs)
	  (set)
	  (let ([x (car xs)]
			[once (occur-once (cdr xs))])
		(if (set-member? once x)
		  (set-remove once x)
		  (set-add once x)))))
  (define (remove-for-lab-blks lab-blks)
	(let* ([scan-block
			 (lambda (lab-blk)
			   (for/fold ([jpif-ref (set)]
						  [jp-ref '()])
				 ([stmt (Block-instr* (cdr lab-blk))] #:when (or (JmpIf? stmt) (Jmp? stmt)))
				 (if (Jmp? stmt)
				   (values jpif-ref (cons (Jmp-target stmt) jp-ref))
				   (values (set-add jpif-ref (JmpIf-target stmt)) jp-ref))))]
		   [tail-labels
			 (for/fold ([acc-jpif-ref (set)]
						[acc-jp-ref '()]
						#:result (set-subtract (occur-once acc-jp-ref) acc-jpif-ref))
			   ([lab-blk lab-blks])
			   (let-values ([(jpif-ref jp-ref) (scan-block lab-blk)])
				 (values (set-union jpif-ref acc-jpif-ref) (append jp-ref acc-jp-ref))))])
	  (letrec ([trans-stmts 
				 (lambda (stmts)
				   (foldr 
					 (lambda (instr acc)
					   (match instr
						 [(Jmp label) (if (set-member? tail-labels label)
										(append (trans-stmts (Block-instr* (dict-ref lab-blks label))) acc)
										(cons instr acc))]
						 [_ (cons instr acc)]))
					 '()
					 stmts))])
		(for/list ([lab-blk lab-blks]
				   #:unless (set-member? tail-labels (car lab-blk)))
		  (match-let ([(Block binfo stmts) (cdr lab-blk)])
			(cons (car lab-blk) (Block binfo (trans-stmts stmts))))))))
  (map-program-def-body remove-for-lab-blks p))

					 

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (define (sizeof type)
	(match type
	  ['Integer 8]))

  (define (alloc-stack info)
	(letrec 
	  ([recur 
		 (lambda (info cur acc)
		   (if (null? info)
			 acc
			 (let ([sym (caar info)] [size (sizeof (cdar info))])
			   (recur (cdr info) (- cur size) (cons (cons sym (- cur size)) acc)))))])
	  (recur info 0 '())))


  (match p
	[(X86Program info `(,lab-blks ...))
	 (let* ([vars-loc 
			  (alloc-stack (let ([var-types (assoc 'locals-types info)]) (if var-types (cdr var-types) '())))]
			[subst-var 
			  (lambda (operand) 
				(if (Var? operand)
				  (match-let ([(Var var) operand]) (Deref 'rbp (cdr (assoc var vars-loc))))
				  operand))]
			[subst-instr
			  (lambda (instr)
				(match instr
					   [(Instr op args)  (Instr op (map subst-var args))]
					   [_ instr]))])
					
	   (if (null? vars-loc)
		 p
		 (X86Program info
					 (map (lambda (lab-blk)
							(cons (car lab-blk) 
								  (match-let ([(Block info stmts) (cdr lab-blk)])
									(Block info (map subst-instr stmts)))))
						  lab-blks))))]))


;objects add to interference graph 
(define (get-infer-objs rands)
  (let ( [infer-obj
		   (lambda (rand)
			 (cond
			   [(or (Var? rand) (Reg? rand)) rand]
			   [(ByteReg? rand) (Reg (byte-reg->full-reg (ByteReg-name rand)))]
			   [(Deref? rand) (Reg (Deref-reg rand))]
			   [(Imm? rand) #f]
			   [(Global? rand) rand]
			   [(FunRef? rand) #f] ;leaq TODO
			   [else (error (format "unhandled operand ~a in get-infer-objs" rand))]))])
	(if (null? rands)
		'()
		(let ([obj (infer-obj (car rands))])
		  (if obj 
			  (cons obj (get-infer-objs (cdr rands)))
			  (get-infer-objs (cdr rands)))))))

(define (get-Gen-Kill instr)
  (let ([rw
		  (match instr
				 [(Instr (or 'addq 'subq) `(,arg1 ,arg2)) 
				  (cons `(,arg1 ,arg2) `(,arg2))]
				 [(Instr (or 'movq 'movzbq 'leaq) `(,arg1 ,arg2)) 
				  (cons `(,arg1) `(,arg2))]
				 [(Instr 'negq `(,e)) (cons `(,e) `(,e))]
				 [(Instr 'set `(,c ,arg2)) (cons '() `(,arg2))]
				 [(Instr 'cmpq rands) (cons rands '())]
				 [(Callq _ arity)
				  (cons (for/list ([x (vector-take arg-registers arity)]) (Reg x)) 
						(for/list ([r caller-save]) (Reg r)))]
				 [(IndirectCallq f arity)
				  (cons (cons f (for/list ([x (vector-take arg-registers arity)]) (Reg x)))
						(for/list ([r caller-save]) (Reg r)))]
				 [(TailJmp f arity)  ; TODO is this right?
				  (cons (cons f (for/list ([x (vector-take arg-registers arity)]) (Reg x)))
						'())] 
				 
				 [_ (error (format "unhandled instr ~a in get-Gen-Kill" instr))])])
	  (cons (apply set (get-infer-objs (car rw))) 
			(apply set (get-infer-objs (cdr rw))))))
				


(define (analyze-dataflow-backward CFG bottom join transfer)
  (let* ([lab-lives (make-hasheq)]
		 [In (make-hasheq)]
		 [Out (make-hasheq)]
		 [worklist (make-queue)])


	;;update one BB
	(define (update lab)
	  (let* ([outs (dict-ref Out lab '())]
			 [tail (for/fold ([acc bottom])
					 ([out outs])
					 (join (dict-ref lab-lives out) acc))]
			 [cur (dict-ref lab-lives lab)]
			 [next (transfer (cons lab cur) tail)])
		(cond 
		  [(equal? cur next) '()]
		  [else (begin 
				  (dict-set! lab-lives lab next)
				  (dict-ref In lab '()))])))

	(begin 
	  ;;init hashes
	  (for ([kv CFG])
		(let ([lab (car kv)]
			  [blk (cdr kv)])
		  ;;init bottom lab-lives
		  (dict-set! lab-lives lab bottom)
		  ;;init worklist queue
		  (enqueue! worklist lab)
		  ;;init In and Out
		  (for ([instr (Block-instr* blk)])
			(match instr
			  [(or (JmpIf _ label) (Jmp label))
			   (dict-set! Out lab (cons label (dict-ref Out lab '())))
			   (dict-set! In label (cons lab (dict-ref In label '())))]
			  [_ (void)]))
		  ))

	  ;;iterate until no more work to do
	  (let iter ()
		(cond 
		  [(queue-empty? worklist) lab-lives]
		  [else
			(let ([new-work (update (dequeue! worklist))])
			  (for ([w new-work]) (enqueue! worklist w))
			  (iter))])))))



(define (uncover-live p)

  (define (uncover-lives CFG)
	(define lab-live-set (make-hasheq))
	(define (uncover-one-instr instr live-after)
	  (match instr
		[(or (? Jmp?) (? JmpIf?) (? Retq?)) live-after]
		[_ (let ([rw (get-Gen-Kill instr)])
			 ((live-after . set-subtract . (cdr rw)) . set-union . (car rw)))]))

	(define (transfer cur tail)
	  (let* ([lab (car cur)]
			 [blk (dict-ref CFG lab)]
			 [last-jmp? (Jmp? (last (Block-instr* blk)))]
			 [acc-lives
			   (for/fold ([acc (if last-jmp? (list tail) (list (set)))])
				 ([instr (Block-instr* blk)])
				 (cond
				   [(and (not last-jmp?) (JmpIf? instr)) (cons (set-union tail (car acc)) acc)]
				   [else (cons (uncover-one-instr instr (car acc)) acc)]))])
		(begin
		  (dict-set! lab-live-set lab acc-lives)
		  (car acc-lives))))

	(begin 
	  (analyze-dataflow-backward CFG (set) set-union transfer)

	  (for/list ([kv CFG])
		(let* ([lab (car kv)]
			   [blk (cdr kv)]
			   [live-set (dict-ref lab-live-set lab)])
		  (cons lab
				(Block (dict-set (Block-info blk) lab live-set) 
					   (Block-instr* blk))))))) ;;uncover-lives

	(map-program-def-body uncover-CFG p))


(define (build-interference p)
  (define (build-from info lab-blks start)
	(let* ([loc-ts (dict-ref info 'locals-types)]
		   [infer-G
			 (foldl 
			   (lambda (v g) (add-vertex! g (Var v)) g) 
			   (undirected-graph '()) 
			   (map car loc-ts))])
	  (letrec 
		([from-label
		   (lambda (label)
			 (match-let* ([(Block binfo instrs) (dict-ref lab-blks label)]
						 [live-sets (dict-ref binfo 'live-set)]
						 [g infer-G])
					(for ([instr instrs]
						  [lives (cdr live-sets)])
						 (match instr

								[(Instr 'movq `(,s ,d)) 
								 (let ([s* (get-infer-objs `(,s))]
									   [d* (get-infer-objs `(,d))])
								   (set-for-each lives 
												 (lambda (x) 
												   (unless (or (and (not (null? s*)) (equal? x (car s*)))
															   (and (not (null? d*)) (equal? x (car d*)))) 
													 (add-edge! g x (car d*))))))]

								[(Instr 'movzbq `(,(ByteReg br) ,d))
								 (let ([fr (Reg (byte-reg->full-reg br))]
									   [d* (get-infer-objs `(,d))])
								   (set-for-each lives (lambda (x) (unless (or (equal? x fr) (equal? x (car d*))) (add-edge! g x (car d*))))))]

								[(JmpIf f lab) (from-label lab)]
								[(Jmp lab) (from-label lab)]

								[(or (Callq f _) (IndirectCallq f _))
								 (set-for-each lives 
											   (lambda (x)
												 (let ([vec?
														 (and (Var? x) 
															  (eq? 'Vector (dict-ref  loc-ts (Var-name x) #f)))])
												   (for ([d (if (and vec? (or (eq? f 'collect) (IndirectCallq? instr)))
																(set-union caller-save callee-save)
																caller-save)])
														(unless (equal? x d) (add-edge! g x (Reg d)))))))]

								[_ (let ([w (cdr (get-Gen-Kill instr))])
									 (set-for-each lives 
												   (lambda (x)
													 (for ([d w] #:unless (equal? x d))
														  (add-edge! g x d)))))]))
					g ))]) ;remember to return g
			  (from-label start))))

  (define (build-from-def def)
	(match-let ([(Def fn ps rt info CFG) def])
			   (Def fn ps rt (cons `(conflicts . ,(build-from info CFG (fn-start-label fn))) info) CFG)))
  (match p
		 [(X86Program info CFG) (X86Program (cons `(conflicts . ,(build-from info CFG 'start)) info) CFG)]
		 [(? ProgramDefs?) (map-program-def build-from-def p)]))


(require "priority_queue.rkt")
(define (color-graph G)
  (let* ([color-map (make-hash)]
		 [get-satur
		   (lambda (v)
			 (let get-color ([us (sequence->stream (in-neighbors G v))] [acc '()])
			   (if (stream-empty? us)
				   (apply set acc)
				   (let ([u (stream-first us)])
					 (cond 
					   [(or (Var? u) (Global? u))
						(if (hash-has-key? color-map u) 
							(get-color (stream-rest us) (cons (hash-ref color-map u) acc))
							(get-color (stream-rest us) acc))]
					   [(Reg? u) (get-color (stream-rest us) (cons (register->color (Reg-name u)) acc))]
					   [else (error (format "unkown object ~a in infer graph" u))])))))]
		 [cmp
		   (lambda (v1 v2)
			 (> (set-count (get-satur v1)) (set-count (get-satur v2))))]
		 [Q (make-pqueue cmp)]
		 [v-h (for/hash ([v (in-vertices G)] #:unless (hash-has-key? color-map v))
						(values v (pqueue-push! Q v)))])

	(let colorize ()
	  (if (= 0 (pqueue-count Q))
		  color-map
		  (let* ([v (pqueue-pop! Q)]
				 [satur (get-satur v)]
				 [reg-k (let find-s-reg ([k 0]) (if (set-member? satur k) 
													(find-s-reg (+ k 1)) 
													k))])
			(hash-set! color-map v reg-k) 
			(pqueue-decrease-key! Q (hash-ref v-h v))
			(colorize))))))

(define (allocate-register p [limit-reg 3]  )

  (define (do-allocate fn start-label info lab-blks)
	(match-let*
	  ([color-map (color-graph (dict-ref info 'conflicts))]

	   [(Block binfo stmts) (dict-ref  lab-blks start-label)]

	   [`(,spilled-bx ,rootst-spilled-bx) `(,(box 0) ,(box 0))]

	   [var-map
		 (let scan-var ([loc-ts (dict-ref info 'locals-types '())] [spilled 0] [rootst-spilled 0])
		   (if (null? loc-ts)
			   (begin (set-box! spilled-bx spilled) (set-box! rootst-spilled-bx rootst-spilled) '())
			   (let* ([var (Var (caar loc-ts))]
					  [ts (cdar loc-ts)]
					  [is-vec-type  (and (pair? ts) (eq? (car ts) 'Vector))])
				 (if (hash-has-key? color-map var)
					 (let ([reg-idx (hash-ref color-map var)])
					   (if (or (< reg-idx 0) (>= reg-idx limit-reg))
						   (if  is-vec-type
								(cons (cons var (Deref rootstack-reg (* -8 (+ 1 rootst-spilled)))) (scan-var (cdr loc-ts) spilled (+ rootst-spilled 1))) ; spill to rootstack for gc
								(cons (cons var (Deref 'rbp (* -8 (+ 1 spilled)))) (scan-var (cdr loc-ts) (+ spilled 1) rootst-spilled)))
						   (cons (cons var (Reg (vector-ref general-registers reg-idx))) (scan-var (cdr loc-ts) spilled rootst-spilled))))
					 (cons (cons var var) (scan-var (cdr loc-ts) spilled))))))]

	   [used-callee-regs 
		 (set-union
		   (for/set ([kv (in-list var-map)] #:when (set-member? callee-save (cdr kv))) (cdr kv))
		   (if (or (= 0 (unbox rootst-spilled-bx)) (not (set-member? callee-save rootstack-reg)))
			   (set)
			   (set (Reg rootstack-reg))))]

	   [replace-instr 
		 (lambda (instr)
		   (let ([replace-rand (lambda (rand) (dict-ref var-map rand rand))])
			 (match instr
					[(Instr op args) (Instr op (map replace-rand args))]
					[(IndirectCallq f arity) (IndirectCallq (replace-rand f) arity)]
					[(TailJmp f arity) (TailJmp (replace-rand f) arity)]
					[_ instr])))]

	   [conclusion-label (string->symbol (~a start-label 'conclusion))]
	   [info^ (append 
				`((num-root-spills . ,(unbox rootst-spilled-bx))
				  (num-stack-spills . ,(unbox spilled-bx))
				  (used-callee-regs . ,used-callee-regs))
				info)]
	   [lab-blks^ (for/list ([lab-blk  lab-blks])
					(let* ([lab (car lab-blk)]
						   [blk (cdr lab-blk)]
						   [stmts* (map replace-instr (Block-instr* blk))]
						   [is-tail (let find ([instrs stmts*])
											   (cond
												 [(null? instrs) #t]
												 [(or (TailJmp? (car instrs)) (Jmp? (car instrs))) #f]
												 [else (find (cdr instrs))]))]
						   [stmts^ (if is-tail
									 (append stmts* `(,(Jmp conclusion-label)))
									 stmts*)])
					  (cons lab (Block (Block-info blk) stmts^))))])

	(values info^ lab-blks^)))

  (define (allocate-for-def def)
	(match-let ([(Def fn ps rt info CFG) def])
			   (let-values ([(info* CFG*) (do-allocate fn (fn-start-label fn) info CFG )])
				 (Def fn ps rt info* CFG*))))

  (match p
		 [(X86Program info lab-blks)
		  (let-values ([(info* lab-blks*) (do-allocate 'main  'start info lab-blks)])
			(X86Program info* lab-blks*))]
		 [(? ProgramDefs?) (map-program-def allocate-for-def p)]))
									

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)

  (define (patch-instr instr)
	(match instr
		   [(Instr 'movq `(,arg ,arg)) '()] ;;del
		   [(Instr 'movq (list (Deref reg1 offset1) (Deref reg2 offset2)))
			`(,(Instr 'movq (list (Deref reg1 offset1) (Reg 'rax)))
			   ,(Instr 'movq (list (Reg 'rax) (Deref reg2 offset2))))]
		   [(Instr 'addq `(,(Deref r1 offset1) ,(Deref r2 offset2)))
			`(,(Instr 'movq `(,(Deref r1 offset1) ,(Reg 'rax)))
			   ,(Instr 'addq `(,(Reg 'rax) ,(Deref r2 offset2))))]
		   [(Instr 'cmpq `(,x ,(Imm n)))
			`(,(Instr 'movq `(,(Imm n) ,(Reg 'rax))) 
			   ,(Instr 'cmpq `(,x ,(Reg 'rax))))]
		   [(Instr 'leaq `(,src ,(and dst (not (? Reg?)))))  ;;dst of leaq must be register
			`(,(Instr 'leaq `(,src ,(Reg 'rax)))
			   ,(Instr 'movq `(,(Reg 'rax) ,dst)))]
		   [(TailJmp (and arg (not (? Reg?))) arity)
			`(,(Instr 'movq `(,arg ,(Reg 'rax)))
			   ,(TailJmp (Reg 'rax) arity))]
		   [(IndirectCallq (and arg (not (? Reg?))) arity)
			`(,(Instr 'movq `(,arg ,(Reg 'rax)))
			   ,(IndirectCallq (Reg 'rax) arity))]
		   [else `(,instr)]))

  (define (patch-CFG lab-blks)
	(for/list ([lab-blk lab-blks])
			  (match-let ([(cons lab (Block binfo stmts)) lab-blk])
						 (cons lab
							   (Block binfo 
									  (foldr 
										(lambda (instr acc)
										  (append (patch-instr instr)  acc))
										'()
										stmts))))))


  (match p
		 [(X86Program info CFG) (X86Program info (patch-CFG CFG))]
		 [(? ProgramDefs?) (map-program-def-body patch-CFG p)]))



;; print-x86 : x86 -> string 
#;(define (print-x86 p)

  (define (print-CFG fn info CFG)
	(let* ([num-root-spills (dict-ref info 'num-root-spills 0)]
		   [num-stack-spills (dict-ref info 'num-stack-spills 0)]
		   [used-callee-regs (dict-ref info 'used-callee-regs 0)]
		   [align-stack-size (* 16 (quotient (+ (* num-stack-spills 8) 15) 16))]
		   [used-rootst-size (* 8 num-root-spills)]
		   [rootstack-size (runtime-config::rootstack-size)]
		   [heap-size (runtime-config::heap-size)]
		   [prelude 
			 (Block '() 
					(append
					  `(,(Instr 'pushq `(,(Reg 'rbp)))
						 ,@(for/list ([reg (in-set used-callee-regs)]) (Instr 'pushq `(,reg))) ;; save callee-saved register
						 ,(Instr 'movq `(,(Reg 'rsp) ,(Reg 'rbp))))
					  (if (not (= 0 align-stack-size))
						`(,(Instr 'subq `(,(Imm align-stack-size) ,(Reg 'rsp)))) ;;reserve stack space
						'())
					  (if (eq? fn 'main) ;;GC init
						`(,(Instr 'movq `(,(Imm rootstack-size)  ,(Reg 'rdi)))
						   ,(Instr 'movq `(,(Imm heap-size) ,(Reg 'rsi)))
						   ,(Callq 'initialize 2))
						'())
					  (if (not (= 0 num-root-spills))
						`(,(Instr 'addq `(,(Imm used-rootst-size) ,(Global  'rootstack_end)))
						  ,(Instr 'movq `(,(Global 'rootstack_end) ,(Reg rootstack-reg)))
						   ,@(if (eq? fn 'main)
							   `(,(Instr 'movq `(,(Imm 0) ,(Deref rootstack-reg 0)))) ;; init rootstack to empty(see runtime.c), only in main 
							   '()))
						'())
					  `(,(Jmp (fn-start-label fn)))))]
		   [conclusion-label (string->symbol (~a (fn-start-label fn) 'conclusion))]
		   [clean-up 
			 (append
			   `(,@(if (not (= 0 num-root-spills))
					 `(,(Instr 'subq `(,(Imm used-rootst-size) ,(Global 'rootstack_end))))
					 '())
				  ,(Instr 'addq `(,(Imm align-stack-size) ,(Reg 'rsp))))
			   `(,@(for/list ([reg (in-set used-callee-regs)]) (Instr `popq `(,reg)))
				  ,(Instr 'popq `(,(Reg 'rbp)))))]
		   [conclude (Block '() (append clean-up `(,(Retq))))]
		   [CFG^ (append `((,fn . ,prelude)
						   (,conclusion-label . ,conclude))
						 CFG)]
		   [print-item
			 (lambda (item)
			   (match item
				 [(Reg r) (~a "%" r)]
				 [(ByteReg br) (~a item)]
				 [(Imm n) (~a "$" n)]
				 [(Global g) (~a  g "(%rip)")]
				 [(Deref r o) (format "~a(%~a)" o r)]
				 [(FunRef label arity) (~a label "(%rip)")]))])

	  (letrec ([instr-printer (lambda (instr)
								(match instr
								  [(Instr 'set `(,cc ,arg)) (format "~a~a ~a" 'set cc (print-item arg))]
								  [(Instr op args) (format "~a ~a" op (string-join (map print-item args) ","))]
								  [(JmpIf f label) (format "~a~a ~a" 'j f label)]
								  [(Jmp label) (~a "jmp " label)]
								  [(TailJmp f arity) 
								   (string-join (append (map instr-printer clean-up) `(,(~a "jmp *%" (Reg-name f)))) "\n\t")]
								  [(Retq) "retq"]
								  [(IndirectCallq f _) (~a "callq *%" (Reg-name f))]
								  [(Callq func _) (~a "callq " func)]))])

	;(string-append (format "\t.global ~a\n\t.align ~a\n" 
	(string-append (format "\t.global ~a\n" 
						   fn)
						   ;(dict-ref info 'align-stack-size))
				   (string-join 
					   (for/list ([lab-blk CFG^])
						 (let ([label (car lab-blk)]
							   [stmts (Block-instr* (cdr lab-blk))])
						   (format "~s:\n\t~a" label (string-join (map instr-printer stmts) "\n\t"))))
					 "\n\n")))))

  (match p
		 [(X86Program info CFG) (print-CFG 'main info CFG)]
		 [(ProgramDefs info defs)
		  (string-join
			(for/list ([def defs]) (print-CFG (Def-name def) (Def-info def) (Def-body def)))
			"\n\n")]))
;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

