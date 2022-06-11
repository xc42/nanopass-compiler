#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rint.rkt")
(require "utilities.rkt")
(require "type-check-Rfun.rkt")
(require "type-check-Cfun.rkt")
(require (prefix-in runtime-config:: "runtime-config.rkt"))
(require graph)
(require racket/promise)
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Rint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Rint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (map-program-def f p)
  (match-let ([(ProgramDefs info defs) p])
			 (ProgramDefs info (map f defs))))

(define-syntax-rule (map-program-def-body f p)
  (map-program-def (lambda (def) 
					 (match-let ([(Def fn ps rt info body) def])
								(Def fn ps rt info (f body))))
				   p))

(define (fn-start-label fn) (string->symbol (~a fn 'start)))

;; R4 -> R4
(define (shrink p)
  (letrec
	([shrink-exp
	   (lambda (e)
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
				[(Let v e body) (Let v (shrink-exp e) (shrink-exp body))]
				[(If cnd thn els) (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
				[(HasType e t) (HasType (shrink-exp e) t)]
				[(Apply f args) (Apply (shrink-exp f) (map shrink-exp args))]
				[_ e]))])
	(match p
		   [(Program info body) (Program info (shrink-exp body))]
		   [(ProgramDefsExp info defs expr) 
			(ProgramDefs info (append
								(for/list ([def (in-list defs)])
											(match-let ([(Def fn ps rt info body) def])
													   (Def fn ps rt info (shrink-exp body))))
								 `(,(Def 'main '() 'Integer '() (shrink-exp expr)))))])))


;; uniquify : R4 -> R4
(define (uniquify p)
  (define (uniquify-exp env)
	(lambda (e)
	  (let ([uniq (uniquify-exp env)])
		(match e
			   [(Var x) (Var (lookup x env))]
			   [(Int n) e]
			   [(Bool b) e]
			   [(HasType e t) (HasType (uniq e) t)]
			   [(Let x e body)
				(let ([x* (gensym x)])
				  (Let x* (uniq e) ((uniquify-exp (extend-env env x x*)) body)))]
			   [(If e1 e2 e3) (If (uniq e1) (uniq e2) (uniq e3))]
			   [(Prim op es) (Prim op (map uniq es))]
			   [(Apply f args) (Apply (uniq f) (map uniq args))]))))
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


;; R4 -> R4
(define (reveal-functions p)
  (let ([fs (map (lambda (def) (Def-name def)) (ProgramDefs-def* p))])
	(letrec ([reveal-functions*
			   (lambda (expr)
				 (match expr
						[(Var v) (let ([f* (member v fs)]) (if  f* (FunRef v) expr))]
						[(HasType e t) (HasType (reveal-functions* e) t)]
						[(Let x e body) (Let x (reveal-functions* e) (reveal-functions* body))]
						[(If e1 e2 e3) (If (reveal-functions* e1) (reveal-functions* e2) (reveal-functions* e3))]
						[(Prim op es) (Prim op (map reveal-functions* es))]
						[(Apply f args) (Apply (reveal-functions* f) (map reveal-functions* args))]
						[_ expr]))])
	  (match p
			 [(? Program?) p]
			 [(? ProgramDefs?) (map-program-def-body reveal-functions* p)]))))
						
; R4 -> R4
(define (limit-functions p)
  (define arg-limit (vector-length arg-registers))

  ;to pack overflowed args to vector need to know their type
  (define expose-apply-type-class
	(class type-check-Rfun-class
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
									 (values e^ (map HasType e* ty*) rt)]
								   [else (error 'type-check "expected a function, not ~a" ty)])))))
		  
	
  (define (limit-Def def)
	(match-let ([(Def fn ps rt info expr) def])
			   (let* ([param-tails (if (> (length ps) arg-limit) 
									   (list-tail ps (- arg-limit 1))
									   '())]
					  [vec-param (gensym 'auto-vec-param)])
				 (letrec ([subst 
							(lambda (targets)
							  (lambda (expr)
								(match expr
									   [(or (? Bool?) (? Int?) (? FunRef?)) expr]
									   [(Var v)
										(let ([idx (index-where targets (lambda (ts) (eq? (car ts) v)))])
										  (if idx
											  (Prim 'vector-ref (list (Var vec-param) (Int idx)))
											  expr))]
									   [(HasType e t) (HasType ((subst targets) e) t)]
									   [(Let x e body) (Let x ((subst targets) e) ((subst (remove x targets)) body))]
									   [(If e1 e2 e3) (If ((subst targets) e1) ((subst targets) e2) ((subst targets) e3))]
									   [(Prim op rands) (Prim op (map (subst targets) rands))]
									   [(Apply f args) 
										(let ([subst.strip (compose (subst targets) HasType-expr)])
										  (Apply 
											((subst targets) f) 
											(if (> (length args) arg-limit)
												(let ([rest-args (list-tail args (- arg-limit 1))])
												  `(,@(map subst.strip (take args (- arg-limit 1)))
													 ,(HasType 
														(Prim 'vector (map subst.strip rest-args))
														`(Vector ,@(map HasType-type rest-args)))))
												(map subst.strip args))))])))])
				   (Def fn 
						(if (> (length ps) arg-limit)
							(append (take ps (- arg-limit 1)) 
									`((,vec-param : ,(cons 'Vector (map last param-tails)))))
							ps)
						rt
						info
						((subst param-tails) expr))))))

  (let ([p^ (send (new expose-apply-type-class) type-check-program p)])
	(match p^
		   [(? Program?) p^]
		   [(ProgramDefs info defs) (ProgramDefs info (map limit-Def defs))])))


(define (expose-allocation p)
  (define (calc-vec-bytes-needed ts)
	(+ 8 ;for vector tag header
	   (foldl 
		 (lambda (t n)
		   (if (pair? t)
			   (+ n (calc-vec-bytes-needed (cdr t)))
			   (+ n 8)))
		 0
		 ts)))

  (define (nested-let-expr vs es body)
	(if (null? es)
		body
		(if (pair? vs)
			(Let (car vs) (car es) (nested-let-expr (cdr vs) (cdr es) body))
			(Let vs (car es) (nested-let-expr vs (cdr es) body)))))

  (define (expose-allocation-expr expr)
	(match expr
		   [(Prim op es) (Prim op (map expose-allocation-expr es))]
		   [(If pred thn els) (If (expose-allocation-expr pred) (expose-allocation-expr thn) (expose-allocation-expr els))]
		   [(Let v e body) (Let v (expose-allocation-expr e) (expose-allocation-expr body))]
		   [(Apply f args) (Apply f (map expose-allocation-expr args))]
		   [(HasType (Prim 'vector es) ts)
			(let* ([vs (map (lambda (x) (gensym 'vec-init)) es)]
				   [bytes (calc-vec-bytes-needed (cdr ts))]
				   [len (length vs)]
				   [assign-body 
					 (let ([var-vec (gensym 'alloc)])
					   (Let  var-vec (Allocate len ts)
							 (nested-let-expr '_ 
											  (let all-assign ([idx 0] [vs* vs])
												(if (null? vs*)
													'()
													(cons (Prim 'vector-set! `(,(Var var-vec) ,(Int idx) ,(Var (car vs*))))
														  (all-assign (+ idx 1) (cdr vs*))))) 
											  (Var var-vec))))]
				   [alloc-body
					 (Let '_ 
						  (If (Prim '< 
									(list (Prim '+ `(,(GlobalValue 'free_ptr) ,(Int bytes)))
										  (GlobalValue 'fromspace_end)))
							  (Void)
							  (Collect bytes))
						  assign-body)])
			  (nested-let-expr vs (map expose-allocation-expr es) alloc-body))]
		   [atm-expr atm-expr]))

  (match p
		 [(Program info e) (Program info (expose-allocation-expr e))]
		 [(? ProgramDefs?) (map-program-def-body expose-allocation-expr p)]))
																				  

			
;; remove-complex-opera* : R4 -> R4
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
		[(If e1 e2 e3) (If (rco-expr e1) (rco-expr e2) (rco-expr e3))] 
		[(Let v e b) (Let v (rco-expr e) (rco-expr b))]
		[(Prim op es) (rco-atm expr)]
		[(Apply f args) (rco-atm expr)] 
		[_ expr]))
  (match p
		 [(Program info expr) (Program info (rco-expr expr))]
		 [(? ProgramDefs?) (map-program-def-body rco-expr p)]))


;; explicate-control : R4 -> C3
(define (explicate-control p)
  (define (explicate-control-expr expr-body start-label)
	(let* ([CFG (list)]
		   [add-CFG
			 (lambda (block [label-str ""])
			   (if (Goto? block)
				   block
				   (let ([label (if (equal? label-str "") (gensym 'block) (string->symbol label-str))])
					 (set! CFG (cons (cons label block) CFG))
					 (Goto label))))]
		   [lz-add-CFG
			 (lambda (block [label-str ""])
			   (delay (add-CFG block label-str)))])
	  (letrec
		([explicate-assign
		   (lambda (var expr acc)
			 (match expr
					[(Let v e body) (explicate-assign v e (explicate-assign var body acc))]
					[(If pred thn els)
					 (let ([acc-label (add-CFG acc)])
					   (explicate-pred pred  
									   (lz-add-CFG (explicate-assign var thn acc-label))
									   (lz-add-CFG (explicate-assign var els acc-label))))]
					[(Apply f args) (Seq (Assign (Var var) (Call f args)) acc)]
					[other (Seq (Assign (Var var) expr) acc)]))]

		 [explicate-pred
		   (lambda (pred lz-thn lz-els)
			 (match pred
					[(Bool #t)  (force lz-thn)]
					[(Bool #f)  (force lz-els)]
					[(Var b) (IfStmt (Prim 'eq? `(,pred ,(Bool #t))) (force lz-thn) (force lz-els))]
					[(Apply f args) 
					 (let ([v (gensym 'auto-if-call)]) 
					   (explicate-assign v (Call f args) (explicate-pred (Var v) lz-thn lz-els)))]
					[(Prim (or 'eq? '< '<= '> '>=) rands) (IfStmt pred (force lz-thn) (force lz-els))]
					[(Prim 'not `(,pred*)) (explicate-pred pred* lz-els lz-thn)]
					[(Let v e body) (explicate-assign v e (explicate-pred body lz-thn lz-els))]
					[(If pred* thn* els*) 
					 (explicate-pred pred* 
									 (lz-add-CFG (explicate-pred thn* lz-thn lz-els)) 
									 (lz-add-CFG (explicate-pred els* lz-thn lz-els)))]))]

		 [explicate-tail
		   (lambda (expr)
			 (match expr
					[(Let var e body) (explicate-assign var e (explicate-tail body))]
					[(If pred thn els) (explicate-pred pred (lz-add-CFG (explicate-tail thn)) (lz-add-CFG (explicate-tail els)))]
					[(Apply f args) (TailCall f args)]
					[other (Return expr)]))])
	  (begin (add-CFG (explicate-tail expr-body) (symbol->string start-label)) CFG))))

	  (match p
			 [(Program info e) (CProgram info (explicate-control-expr e 'start))]
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

  (define (get-vec-tag len ts)
	(let ([mask (let pointer-mask ([ts* (cdr ts)])
				 (if (null? ts*)
					 0
					 (bitwise-ior (arithmetic-shift (pointer-mask (cdr ts*)) 1) (if (pair? (car ts)) 1 0))))]
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

  (define (trans-assign stmt)
	(match-let ([(Assign dst expr) stmt])
	   (match expr
		 [(Int n) `(,(Instr 'movq (list (Imm n) dst)))]
		 [(Bool b) `(,(Instr 'movq (list (Imm (if b 1 0)) dst)))]
		 [(Var v) `(,(Instr 'movq (list (Var v) dst)))]
		 [(GlobalValue var) `(,(Instr 'movq (list (Global var) dst)))]
		 [(Void) `(,(Instr 'movq (list (Imm 0) dst)))]
		 [(FunRef f) `(,(Instr 'leaq (list expr dst)))]
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
		  
		 [(Prim '+ `(,e1 ,e2))
		  (cond
			[(and (Int? e1) (Int? e2)) 
			 (match-let ([(Int n1) e1] [(Int n2) e2]) `(,(Instr 'movq (list (Imm (+ n1 n2)) dst))))] 
			[(or (Int? e1) (Int? e2))
			 (match-let ([(Int n) (if (Int? e1) e1 e2)] [(Var v) (if (Int? e2) e1 e2)] [(Var var) dst]) 
			   (if (eq? v var) 
				 `(,(Instr 'addq (list (Imm n) dst)))
				 `(,(Instr 'movq (list (Var v) dst)) ,(Instr 'addq (list (Imm n) dst)))))]
			[else 
			  (match-let ([(Var v1) e1] [(Var v2) e2] [(Var var) dst])
				(cond
				  [(eq? v1 var) `(,(Instr 'addq (list e2 dst)))]
				  [(eq? v2 var) `(,(Instr 'addq (list e1 dst)))]
				  [else `(,(Instr 'movq (list e1 dst)) ,(Instr 'addq (list e2 dst)))]))])]
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
		 [(Allocate len ts)
		  (list (Instr 'movq `(,(Global 'free_ptr) ,(Reg 'r11)))
				(Instr 'addq `(,(Imm (* 8 (+ len 1))) ,(Global 'free_ptr)))
				(Instr 'movq `(,(Imm (get-vec-tag len ts)) ,(Deref 'r11 0)))
				(Instr 'movq `(,(Reg 'r11) ,dst)))]
		 [(Collect bytes)
		  (list (Instr 'movq `(,(Reg rootstack-reg) ,(Global 'rootstack_end))) ;;mannually spill rootstack-reg to memory
				(Instr 'movq `(,(Reg rootstack-reg) ,(Reg 'rdi)))
				(Instr 'movq `(,(Imm bytes) ,(Reg 'rsi)))
				(Callq 'collect 2))])))

  
  (define (trans-stmts stmts)
	(match stmts
		   [(Goto label) `(,(Jmp label))]
		   [(Seq s1 tail) (append (trans-assign s1) (trans-stmts tail))]
		   [(TailCall f args) `(,@(push-args args)
								 ,(TailJmp f (length args)))]
		   [(IfStmt pred thn els)
			(match-let ([(Prim op `(,e1 ,e2))  pred])
					   (let ([v1 (to-X86-val e1)]
							 [v2 (to-X86-val e2)]
							 [flag (cdr (cmpop->flag op))])
						 `(,(Instr 'cmpq (list v2 v1)) ,(JmpIf flag (Goto-label thn)) ,(Jmp (Goto-label els)))))]
		   [(Return expr) (match expr
								 [(Prim '+ `(,(Int n1) ,(Int n2))) 
								  `(,(Instr 'movq (list (Imm (+ n1 n2)) (Reg 'rax))))]
								 [(Prim '+ `(,(Int n1) ,e2))
								  `(,(Instr 'movq (list (Imm n1) (Reg 'rax))) ,(Instr 'addq (list e2 (Reg 'rax))))]
								 [(Prim '+ `(,e1 ,(Int n2)))
								  `(,(Instr 'movq (list e1 (Reg 'rax))) ,(Instr 'addq (list (Imm n2) (Reg 'rax))))]
								 [(Prim '+ `(,e1 ,e2))
								  `(,(Instr 'movq (list e1 (Reg 'rax))) ,(Instr 'addq (list e2 (Reg 'rax))))]
								 [(Prim 'vector-ref `(,v ,i))
								  (list (Instr 'movq `(,v ,(Reg 'r11)))
										(Instr 'movq `(,(Deref 'r11 (* 8 (+ (Int-value i) 1))) ,(Reg 'rax))))]
								 [(Prim '- `(,e))
								  (if (Int? e)
									  (match-let ([(Int n) e]) `(,(Instr 'movq (list (Imm (- n)) (Reg 'rax)))))
									  `(,(Instr 'movq (list e (Reg 'rax))) ,(Instr 'negq (list (Reg 'rax)))))]
								 [(Int n) `(,(Instr 'movq (list (Imm n) (Reg 'rax))))]
								 [_ `(,(Instr 'movq (list expr (Reg 'rax))))])]))

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
											 (Block '() (append arg-pass-stmts (trans-stmts stmts)))
											 (Block '() (trans-stmts stmts))))))])
				 (Def fn ps rt info^ CFG^))))


  (match (type-check-Cfun p)
	[(CProgram info CFG) 
	 (X86Program (cons `(num-root-spills . ,(num-root-spills info)) info)
				 (for/list ([bb CFG]) 
						   (cons (car bb) 
								 (Block '() (trans-stmts (cdr bb))))))]
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
  (match p
		 [(X86Program info lab-blks) (X86Program info (remove-for-lab-blks lab-blks))]
		 [(? ProgramDefs?) (map-program-def-body remove-for-lab-blks p)]))

					 

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

(define (get-instr-RW-set instr)
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
				 
				 [_ (error (format "unhandled instr ~a in get-instr-RW-set" instr))])])
	  (cons (apply set (get-infer-objs (car rw))) 
			(apply set (get-infer-objs (cdr rw))))))
				

;two ways:  1. calculate CFG and using tsort to get eval order
;			2. using lazy eval
(define (uncover-live p)
  (define (uncover-CFG lab-blks)
	(letrec ([uncover-one-instr
			   (lambda (instr acc-live-set)
				 (let ([live-after (car acc-live-set)])
				   (match instr
						  [(Instr 'cmpq rands) 
						   (for/fold ([lives (set-union live-after (cadr acc-live-set))]) ;;here assume cmp followed by JmpIf and Jmp
									 ([x (car (get-instr-RW-set instr))])
									 (set-add lives x))]
						  [(Jmp label) (car (force (dict-ref lazy-lab-live-sets label)))]
						  [(JmpIf c label) (car (force (dict-ref lazy-lab-live-sets label)))]
						  [(Retq) live-after] ;;TODO
						  [_ (let ([rw (get-instr-RW-set instr)])
							   (set-union (set-subtract live-after (cdr rw)) (car rw)))] 
						  )))]
			 [uncover-block	
			   (lambda (stmts) 
				 (foldr (lambda (instr acc-live-set) (cons (uncover-one-instr instr acc-live-set) acc-live-set))
						`(,(set))
						stmts))]
			 [lazy-lab-live-sets
			   (map 
				 (lambda (lab-blk)
				   (let ([lab (car lab-blk)] 
						 [blk (cdr lab-blk)])
					 (cons lab (delay (uncover-block (Block-instr* blk))))))
				 lab-blks)])
	  (map 
		(lambda (lab-blk) 
		  (match-let ([(cons label (Block info stmts)) lab-blk])
					 (cons label 
						   (Block 
							 (cons (cons 'live-set (force (dict-ref lazy-lab-live-sets label))) 
										info) 
							 stmts))))
		lab-blks)))
  (match p
		 [(X86Program info lab-blks) (X86Program info (uncover-CFG lab-blks))]
		 [(? ProgramDefs?) (map-program-def-body uncover-CFG p)]))


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

								[_ (let ([w (cdr (get-instr-RW-set instr))])
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

(define (allocate-register p [limit-reg 3] [rootstack-size (runtime-config::rootstack-size)] [heap-size (runtime-config::heap-size)])

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
			   
	   [`(,used-stack-size ,used-rootst-size) `(,(* 8 (unbox spilled-bx)) ,(* 8 (unbox rootst-spilled-bx)))]

	   [align-stack-size (* 16 (quotient (+ used-stack-size 15) 16))]

	   [replace-instr 
		 (lambda (instr)
		   (let ([replace-rand (lambda (rand) (dict-ref var-map rand rand))])
			 (match instr
					[(Instr op args) (Instr op (map replace-rand args))]
					[(IndirectCallq f arity) (IndirectCallq (replace-rand f) arity)]
					[(TailJmp f arity) (TailJmp (replace-rand f) arity)]
					[_ instr])))]

	   [conclusion-label (string->symbol (~a start-label 'conclusion))])

	(values (append 
			  `((num-root-spills . ,(unbox rootst-spilled-bx))
				(align-stack-size . ,align-stack-size)
				(used-callee-regs . ,used-callee-regs))
				info)
			(cons
			  (cons fn
					(Block '() (append
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
								 (if (not (= 0 (unbox rootst-spilled-bx)))
									 `(,(Instr 'movq `(,(Global  'rootstack_end) ,(Reg rootstack-reg)))
										,@(if (eq? fn 'main)
											  `(,(Instr 'movq `(,(Imm 0) ,(Deref rootstack-reg 0)))) ;; init rootstack to empty(see runtime.c), only in main 
											  '())
										,(Instr 'addq `(,(Imm used-rootst-size) ,(Reg rootstack-reg))))
									 '())
									`(,(Jmp start-label)))))
			  (cons 
				(cons conclusion-label
					  (Block '() (append
								   `(,@(if (not (= 0 (unbox rootst-spilled-bx)))
										   `(,(Instr 'subq `(,(Imm used-rootst-size) ,(Reg rootstack-reg)))
											  ,(Instr 'movq `(,(Reg rootstack-reg) ,(Global 'rootstack_end)))) 
										   '())
									  ,(Instr 'addq `(,(Imm align-stack-size) ,(Reg 'rsp))))
								   `(,@(for/list ([reg (in-set used-callee-regs)]) (Instr `popq `(,reg)))
									 ,(Instr 'popq `(,(Reg 'rbp)))
									  ,(Retq)))))
				(map 
				  (let ([tails 
						  (let find-tails ([label start-label])
							(let* ([stmts (Block-instr* (dict-ref lab-blks label))]
								   [jmps (for/list ([stmt stmts] #:when (or (JmpIf? stmt) (Jmp? stmt)))
												   (match stmt
														  [(JmpIf _ next) next]
														  [(Jmp next) next]))])
							  (if (null? jmps)
								  (set label)
								  (apply set-union (cons (set label) (map find-tails jmps))))))])

					(lambda (lab-blk)
					  (match-let ([(cons lab* (Block binfo* stmts*)) lab-blk])
								 (if (set-member? tails lab*)
									 (cons lab* (Block binfo* (append (map replace-instr stmts*) `(,(Jmp conclusion-label)))))
									 (cons lab* (Block binfo* (map replace-instr stmts*)))))))
				  lab-blks))))))

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
(define (print-x86 p)
  (define (instr-printer info)
	(let ([num-root-spills (dict-ref info 'num-root-spills 0)]
		  [align-stack-size (dict-ref info 'align-stack-size 0)]
		  [used-callee-regs (dict-ref info 'used-callee-regs 0)]
		  [print-item
			(lambda (item)
			  (match item
					 [(Reg r) (~a "%" r)]
					 [(ByteReg br) (~a item)]
					 [(Imm n) (~a "$" n)]
					 [(Global g) (~a  g "(%rip)")]
					 [(Deref r o) (format "~a(%~a)" o r)]
					 [(FunRef label) (~a label "(%rip)")]))])
	  (letrec 
		([print-instr
		   (lambda (instr)
			 (match instr
					[(Instr 'set `(,cc ,arg)) (format "~a~a ~a" 'set cc (print-item arg))]
					[(Instr op args) (format "~a ~a" op (string-join (map print-item args) ","))]
					[(JmpIf f label) (format "~a~a ~a" 'j f label)]
					[(Jmp label) (~a "jmp " label)]
					[(TailJmp f arity) 
					 (let ([clean-up 
							 `(,(Instr 'subq `(,(Imm num-root-spills) ,(Reg rootstack-reg)))
								,(Instr 'addq `(,(Imm align-stack-size) ,(Reg 'rsp)))
								,@(for/list ([reg (in-set used-callee-regs)]) (Instr `popq `(,reg)))
								,(Instr 'popq `(,(Reg 'rbp))))])
					   (string-join (append (map print-instr clean-up) `(,(~a "jmp *%" (Reg-name f)))) "\n\t"))]
					[(Retq) "retq"]
					[(IndirectCallq f _) (~a "callq *%" (Reg-name f))]
					[(Callq func _) (~a "callq " func)]))])
		print-instr)))

  (define (print-CFG entry info CFG)
	;(string-append (format "\t.global ~a\n\t.align ~a\n" 
	(string-append (format "\t.global ~a\n" 
						   entry)
						   ;(dict-ref info 'align-stack-size))
				   (string-join 
					 (map
					   (lambda (lab-blk)
						 (let ([label (car lab-blk)]
							   [stmts (Block-instr* (cdr lab-blk))])
						   (format "~s:\n\t~a" label (string-join (map (instr-printer info) stmts) "\n\t"))))
					   CFG)
					 "\n\n")))

  (match p
		 [(X86Program info CFG) (print-CFG 'main info CFG)]
		 [(ProgramDefs info defs)
		  (string-join
			(for/list ([def defs]) (print-CFG (Def-name def) (Def-info def) (Def-body def)))
			"\n\n")]))
