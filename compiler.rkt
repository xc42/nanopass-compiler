#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rint.rkt")
(require "utilities.rkt")
(require "type-check-Cvec.rkt")
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


;; R3 -> R3
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
						  ['<= (If (Prim '< new-es) T (If (Prim 'eq? new-es) T F))]
						  ['>= (Prim 'not `(,(Prim '< new-es)))]
						  ['>  (If (Prim 'not `(,(Prim '< new-es))) (If (Prim 'eq? new-es) F T) F)]
						  [other (Prim op new-es)]))]
				[(Let v e body) (Let v (shrink-exp e) (shrink-exp body))]
				[(If cnd thn els) (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
				[(HasType e t) (HasType (shrink-exp e) t)]
				[_ e]))])
	(match p
		   [(Program info e) (Program info (shrink-exp e))])))


;; uniquify : R3 -> R3
(define (uniquify p)
  (define (uniquify-exp env)
	(lambda (e)
	  (match e
			 [(Var x)
			  (Var (lookup x env))]
			 [(Int n) e]
			 [(Bool b) e]
			 [(HasType e t) (HasType ((uniquify-exp env) e) t)]
			 [(Let x e body)
			  (let ([x* (gensym x)])
				(Let x* ((uniquify-exp env) e) ((uniquify-exp (extend-env env x x*)) body)))]
			 [(If e1 e2 e3) (If ((uniquify-exp env) e1) ((uniquify-exp env) e2) ((uniquify-exp env) e3))]
			 [(Prim 'read '()) e]
			 [(Prim op es)
			  (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))
  (match p
		 [(Program info e) (Program info ((uniquify-exp '()) e))]))

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

  (match-let ([(Program info e) p])
			 (Program info (expose-allocation-expr e))))
																				  

			
;; remove-complex-opera* : R3 -> R3
(define (remove-complex-opera* p)
  (define (rco-atm expr)
	(match expr
		[(Prim op es)
		 (let nested-let ([es* es] [rand-acc '()])
		   (if (null? es*)
			   (Prim op (reverse rand-acc))
			   (let ([e (car es*)])
				 (if (atm? e)
					 (nested-let (cdr es*) (cons e rand-acc))
					 (let ([v (gensym 'tmp)])
					   (Let v (rco-expr e) (nested-let (cdr es*) (cons (Var v) rand-acc))))))))]))

  (define (rco-expr expr)
	(match expr
		[(If e1 e2 e3) (If (rco-expr e1) (rco-expr e2) (rco-expr e3))] 
		[(Let v e b) (Let v (rco-expr e) (rco-expr b))]
		[(Prim op es) (rco-atm expr)]
		[_ expr]))
  (match-let ([(Program info expr) p])
	(Program info (rco-expr expr))))

;; explicate-control : R1 -> C0
(define (explicate-control p)
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
				  [other (Seq (Assign (Var var) expr) acc)]))]

	   [explicate-pred
		 (lambda (pred lz-thn lz-els)
		   (match pred
				  [(Bool #t)  (force lz-thn)]
				  [(Bool #f)  (force lz-els)]
				  [(Var b) (IfStmt (Prim 'eq? `(,pred ,(Bool #t))) (force lz-thn) (force lz-els))]
				  [(Prim (or 'eq? '<) rands) (IfStmt pred (force lz-thn) (force lz-els))]
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
				  [other (Return expr)]))])
	  (match p
			 [(Program info e)
			  (CProgram info (begin (add-CFG (explicate-tail e) "start") CFG))]))))

       

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
				  
				
  (define (trans-C0-assign stmt)
	(match-let ([(Assign dst expr) stmt])
	   (match expr
		 [(Int n) `(,(Instr 'movq (list (Imm n) dst)))]
		 [(Bool b) `(,(Instr 'movq (list (Imm (if b 1 0)) dst)))]
		 [(Var v) `(,(Instr 'movq (list (Var v) dst)))]
		 [(GlobalValue var) `(,(Instr 'movq (list (Global var) dst)))]
		 [(Void) `(,(Instr 'movq (list (Imm 0) dst)))]

		 [(Prim 'read '()) `(,(Callq 'read_int 0) ,(Instr 'movq (list (Reg 'rax) dst)))]
		 [(Prim 'not `(,e)) 
		  (match e
				 [(Bool b) `(,(Instr 'movq (list(Imm (if b 0 1)) dst)))]
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
				(Instr 'movq `(,arg ,(Deref 'r11 (* 8 (+ (Int-value i) 1)))))
				(Instr 'movq `(,(Imm 0) ,dst)))]
		 [(Prim (or 'eq? '<) `(,e1 ,e2))
		  (let-values ([(op cc) (if (eq? (Prim-op expr) 'eq?) 
									   (values equal? 'e)
									   (values < 'l))])
			(cond 
			  [(and (constant? e1) (constant? e2)) `(,(Instr 'movq (list (Imm (if (op (get-const-val e1) (get-const-val e2)) 1 0)) dst)))]
			  [else `(,(Instr 'cmpq `(,(to-X86-val e2) ,(to-X86-val e1))) 
					  ,(Instr 'set (list cc (Reg 'al))) 
					  ,(Instr 'movzbq (list (Reg 'al) dst)))]))]
		 [(Allocate len ts)
		  (list (Instr 'movq `(,(Global 'free_ptr) ,(Reg 'r11)))
				(Instr 'addq `(,(Imm (* 8 (+ len 1))) ,(Global 'free_ptr)))
				(Instr 'movq `(,(Imm (get-vec-tag len ts)) ,(Deref 'r11 0)))
				(Instr 'movq `(,(Reg 'r11) ,dst)))]
		 [(Collect bytes)
		  (list (Instr 'movq `(,(Reg rootstack-reg) ,(Reg 'rdi)))
				(Instr 'movq `(,(Imm bytes) ,(Reg 'rsi)))
				(Callq 'collect 2))])))

  
  (define (trans-stmts stmts)
	(match stmts
		   [(Goto label) `(,(Jmp label))]
		   [(Seq s1 tail) (append (trans-C0-assign s1) (trans-stmts tail))]
		   [(IfStmt pred thn els)
			(match-let ([(Prim op `(,e1 ,e2))  pred])
					   (let ([v1 (to-X86-val e1)]
							 [v2 (to-X86-val e2)]
							 [flag (match op
										  ['eq? 'e]
										  ['< 'l])])
						 `(,(Instr 'cmpq (list v2 v1)) ,(JmpIf flag (Goto-label thn)) ,(Jmp (Goto-label els)))))]
		   [(Return expr) (match expr
								 [(Prim '+ `(,e1 ,e2)) 
								  (cond
									[(and (Int? e1) (Int? e2)) 
									 (match-let ([(Int n1) e1] [(Int n2) e2]) `(,(Instr 'movq (list (Imm (+ n1 n2)) (Reg 'rax)))))]
									[(Int? e1) (match-let ([(Int n1) e1]) 
														  `(,(Instr 'movq (list (Imm n1) (Reg 'rax))) ,(Instr 'addq (list e2 (Reg 'rax)))))]
									[(Int? e2) (match-let ([(Int n2) e2]) 
														  `(,(Instr 'movq (list e1 (Reg 'rax))) ,(Instr 'addq (list (Imm n2) (Reg 'rax)))))]
									[else `(,(Instr 'movq (list e1 (Reg 'rax))) ,(Instr 'addq (list e2 (Reg 'rax))))])]
								 [(Prim 'vector-ref `(,v ,i))
								  (list (Instr 'movq `(,v ,(Reg 'r11)))
										(Instr 'movq `(,(Deref 'r11 (* 8 (+ (Int-value i) 1))) ,(Reg 'rax))))]
								 [(Prim '- `(,e))
								  (if (Int? e)
									  (match-let ([(Int n) e]) `(,(Instr 'movq (list (Imm (- n)) (Reg 'rax)))))
									  `(,(Instr 'movq (list e (Reg 'rax))) ,(Instr 'negq (list (Reg 'rax)))))]
								 [(Int n) `(,(Instr 'movq (list (Imm n) (Reg 'rax))))]
								 [_ `(,(Instr 'movq (list expr (Reg 'rax))))])]))
  (match (type-check-Cvec p)
	[(CProgram info (list lab-sts ...))
	 (X86Program info
				 (map 
				   (lambda (ls)
					 (let ([label (car ls)] [stmts (cdr ls)])
					   (cons label (Block '() (trans-stmts stmts)))))
				   lab-sts))]))

(define (remove-jumps p)
  (define (occur-once xs)
	(if (null? xs)
		(set)
		(let ([x (car xs)]
			  [once (occur-once (cdr xs))])
		  (if (set-member? once x)
			  (set-remove once x)
			  (set-add once x)))))
  (let* ([lab-blks (X86Program-CFG p)]
		 [scan-block
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
	(letrec
	  ([trans-stmts
		 (lambda (stmts)
		   (foldr 
			 (lambda (instr acc)
			   (match instr
					  [(Jmp label) (if (set-member? tail-labels label)
									   (append (trans-stmts (Block-instr* (cdr (assoc label lab-blks)))) acc)
									   (cons instr acc))]
					  [_ (cons instr acc)]))
			 '()
			 stmts))])
	  (match-let ([(X86Program info lab-blks) p])
				 (X86Program info
							 (for/list ([lab-blk lab-blks]
										#:unless (set-member? tail-labels (car lab-blk)))
									   (match-let ([(Block binfo stmts) (cdr lab-blk)])
												  (cons (car lab-blk) (Block binfo (trans-stmts stmts))))))))))

					 

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

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (let ([patch-instr
		  (lambda (instr)
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
				   [else `(,instr)]))])
	(match p
	  [(X86Program info `(,lab-blks ...))
	   (X86Program info (map 
						  (lambda (lab-blk)
							(cons (car lab-blk)
								  (match-let ([(Block info stmts) (cdr lab-blk)])
									(Block info 
										   (foldr (lambda (cur acc) (append (patch-instr cur) acc)) 
												  '() 
												  stmts)))))
						  lab-blks))])))



(define (get-instr-RW-set instr)
  (lambda (instr)
	(match instr
		   [(Instr (or 'addq 'subq) `(,arg1 ,arg2)) 
			(if (Imm? arg1) 
				(cons (set arg2) (set)) 
				(cons (set arg1 arg2) (set)))]
		   [(Instr 'movq `(,arg1 ,arg2)) 
			(if (Imm? arg1) 
				(cons (set) (set arg2))
				(cons (set arg1) (set arg2)))]
		   [(Instr 'negq `(,e)) (cons (set e) (set))]
		   [(Instr 'jmp `(,label)) (cons (set) (set))] ;;TODO
		   [(Callq label _) (cons (set) (apply set (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11))))] ;;TODO
		   [(Retq) (cons (set) (set))] ;;TODO
		   )))

;two ways:  1. calculate CFG and using tsort to get eval order
;			2. using lazy eval
(define (uncover-live p)
  (match-letrec ([(X86Program info lab-blks) p]
				 [uncover-one-instr
				   (lambda (instr acc-live-set)
					 (let ([live-after (car acc-live-set)])
					   (match instr
							  [(Instr (or 'addq 'subq) `(,arg1 ,arg2)) 
							   (if (Imm? arg1) 
								   (set-add live-after arg2) 
								   (set-union live-after (set arg1 arg2)))]
							  [(Instr (or 'movq 'movzbq) `(,arg1 ,arg2)) 
							   (if (Imm? arg1) 
								   (set-remove live-after arg2)
								   (set-add (set-remove live-after arg2) arg1))]
							  [(Instr 'negq `(,e)) (set-add live-after e)]
							  [(Instr 'cmpq rands) 
							   (foldl (lambda (e st) (if (not (Imm? e)) (set-add st e) st))
									  (set-union live-after (cadr acc-live-set)) ;;here assume cmp followed by JmpIf and Jmp
									  rands)]
							  [(Instr 'set `(,c ,arg2)) (set-remove live-after arg2)]
							  [(Jmp label) (car (force (cdr (assoc label lazy-lab-live-sets))))]
							  [(JmpIf c label) (car (force (cdr (assoc label lazy-lab-live-sets))))]
							  [(Callq label arity) (set-union (set-remove live-after (set-map caller-save Reg))
															  (vector->set (vector-take arg-registers arity)))] 
							  [(Retq) live-after] ;;TODO
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
				(X86Program info
							(map 
							  (lambda (lab-blk) 
								(match-let ([(cons label (Block info stmts)) lab-blk])
										   (cons label (Block (cons (cons 'live-set (force (cdr (assoc label lazy-lab-live-sets)))) info) stmts))))
							  lab-blks))))

(define (build-interference p)
  (match-let* ([(X86Program info lab-blks) p]
			   [loc-ts (assoc 'locals-types info)]
			   [infer-G
				 (foldl 
				   (lambda (v g) (add-vertex! g (Var v)) g) 
				   (undirected-graph '()) 
				   (map car (cdr loc-ts)))])
			  (define (graph-from label)
				(match-let* ([`(,label . ,(Block binfo instrs)) (assoc label lab-blks)]
							 [`(live-set . ,live-sets) (assoc 'live-set binfo)]
							 [g infer-G])
							(for ([instr instrs]
								  [lives (cdr live-sets)])
								 (match instr
										[(Instr 'movq `(,s ,d)) 
										 (set-for-each lives (lambda (x) (unless (or (equal? x s) (equal? x d)) (add-edge! g x d))))]
										[(Instr 'movzbq `(,(Reg 'al) ,d))
										 (set-for-each lives (lambda (x) (unless (or (equal? x (Reg 'rax)) (equal? x d)) (add-edge! g x d))))]
										[(Instr (or 'addq 'subq) `(,s ,d))
										 (set-for-each lives (lambda (x) (unless (equal? x d) (add-edge! g x d))))]
										[(Instr 'cmpq rands)
										 (void)] ;no write, do nothing
										[(Instr 'set `(,cc ,(Reg 'al))) 
										 (set-for-each lives (lambda (x) (unless (equal? x (Reg 'rax)) (add-edge! g x (Reg 'rax)))))]
										[(Instr 'negq `(,d))
										 (set-for-each lives (lambda (x) (unless (equal? x d) (add-edge! g x d))))]
										[(JmpIf f lab) (graph-from lab)]
										[(Jmp lab) (graph-from lab)]
										[(Callq label arity) 
										 (if (eq? label 'collect)
											 (set-for-each lives 
														   (lambda (x)
															 (let ([is-vec-type
																	 (and (Var? x) 
																		  (let ([ts (assoc (Var-name x) loc-ts)])
																			(and ts (pair? ts) (eq? 'Vector (cadr ts)))))])
															   (for ([d (if is-vec-type (set-union caller-save callee-save) caller-save)])
																	(unless (equal? x d) (add-edge! g x (Reg d)))))))
											 (set-for-each lives 
														   (lambda (x) 
															 (for ([d caller-save]) 
																  (unless (equal? x d) (add-edge! g x (Reg d)))))))]))))
			  (graph-from 'start)
			  (X86Program (cons (cons 'conflicts infer-G) info) lab-blks)))


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
					   [(Var? u) 
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

(define (allocate-register P [limit-reg 3] [rootstack-size (* 8 32)] [heap-size 4096])
  (match-let* ([(X86Program info lab-blks) P]
			   [color-map (color-graph (cdr (assoc 'conflicts info)))]
			   [(Block binfo stmts) (cdr (assoc 'start lab-blks))]
			   [`(,spilled-bx ,rootst-spilled-bx) `(,(box 0) ,(box 0))]
			   [var-map
				 (let scan-var ([loc-ts (cdr (assoc 'locals-types info))] [spilled 0] [rootst-spilled 0])
				   (if (null? loc-ts)
					   (begin (set-box! spilled-bx spilled) (set-box! rootst-spilled-bx rootst-spilled) '())
					   (let* ([var (Var (caar loc-ts))]
							  [ts (cdar loc-ts)]
							  [is-vec-type  (and (pair? ts) (eq? (car ts) 'Vector))])
						 (if (hash-has-key? color-map var)
							 (let ([reg-idx (hash-ref color-map var)])
							   (if (or (< reg-idx 0) (>= reg-idx limit-reg))
								   (if  is-vec-type
									 (cons (cons var (Deref rootstack-reg (* 8 (+ 1 rootst-spilled)))) (scan-var (cdr loc-ts spilled (+ rootst-spilled 1)))) ; spill to rootstack for gc
									 (cons (cons var (Deref 'rbp (* -8 (+ 1 spilled)))) (scan-var (cdr loc-ts) (+ spilled 1) rootst-spilled)))
								   (cons (cons var (Reg (vector-ref general-registers reg-idx))) (scan-var (cdr loc-ts) spilled rootst-spilled))))
							 (cons (cons var var) (scan-var (cdr loc-ts) spilled))))))]
			   [used-callee-regs (for/set ([kv (in-list var-map)] #:when (set-member? callee-save (cdr kv))) (cdr kv))]
			   [used-stack-size (* 8 (unbox spilled-bx))]
			   [align-stack-size (* 16 (quotient (+ used-stack-size 15) 16))]
			   [replace-instr 
				 (lambda (instr)
				   (match instr
						  [(Instr op args) 
						   (Instr op (map (lambda (arg) 
											(let ([pr (assoc arg var-map)])
											  (if pr (cdr pr) arg)))
										  args))]
						  [_ instr]))])
			  (X86Program info 
						  (cons
							(cons 'main
								  (Block '() (append
											   `(,(Instr 'pushq `(,(Reg 'rbp)))
												 ,(Instr 'movq `(,(Reg 'rsp) ,(Reg 'rbp))))
											   (for/list ([reg (in-set used-callee-regs)]) (Instr 'pushq `(,reg)))
											   `(,(Instr 'subq `(,(Imm align-stack-size) ,(Reg 'rsp)))
												 ,(Instr 'movq `(,(Imm rootstack-size)  ,(Reg 'rdi)))
												 ,(Instr 'movq `(,(Imm heap-size) ,(Reg 'rsi)))
												 ,(Callq 'initialize 2)
												 ,(Instr 'movq `(,(Global  'rootstack_begin) ,(Reg rootstack-reg)))
												 ,(Instr 'movq `(,(Imm 0) ,(Deref rootstack-reg 0)))
												 ,(Instr 'addq `(,(Imm (unbox rootst-spilled-bx)) ,(Reg rootstack-reg)))
											     ,(Jmp 'start)))))
							(cons 
							  (cons 'conclusion 
									(Block '() (append
												 `(,(Instr 'subq `(,(Imm (unbox rootst-spilled-bx)) ,(Reg rootstack-reg)))
												   ,(Instr 'addq `(,(Imm align-stack-size) ,(Reg 'rsp))))
												 (for/list ([reg (in-set used-callee-regs)]) (Instr `popq `(,reg)))
												 `(,(Instr 'popq `(,(Reg 'rbp)))
												   ,(Retq)))))
							  (map 
								(let ([tails 
										(let find-tails ([label 'start])
										  (let* ([stmts (Block-instr* (cdr (assoc label lab-blks)))]
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
												   (cons lab* (Block binfo* (append (map replace-instr stmts*) `(,(Jmp 'conclusion)))))
												   (cons lab* (Block binfo* (map replace-instr stmts*)))))))
								lab-blks))))))

;; print-x86 : x86 -> string 
(define (print-x86 p)
  (define (print-instr instr)
	(let ([print-item
			(lambda (item)
			  (match item
				[(Reg r) (~a "%" r)]
				[(Imm n) (~a "$" n)]
				[(Global g) (~a  g "(%rip)")]
				[(Deref r o) (format "~a(%~a)" o r)]))])
	(match instr
	  [(Instr 'set `(,cc ,arg)) (format "~a~a ~a" 'set cc (print-item arg))]
	  [(Instr op args) (format "~a ~a" op (string-join (map print-item args) ","))]
	  [(JmpIf f label) (format "~a~a ~a" 'j f label)]
	  [(Jmp label) (~a "jmp " label)]
	  [(Retq) "retq"]
	  [(Callq func _) (~a "callq " func)])))

  (match-let* ([(X86Program info lab-blks) p]
			   [(Block _ instrs) (cdr (assoc 'start lab-blks))]
			   [stack-size (* (length (assoc 'locals-types info)) 8)])
	(string-join 
	  (map
		(lambda (lab-blk)
		  (let* ([label (car lab-blk)]
				 [stmts (Block-instr* (cdr lab-blk))]
				 [instr-strs (format "~s:\n\t ~a" label (string-join (map print-instr stmts) "\n\t"))])
			(if (eq? label 'main)
				(string-append "\t.global main\n" instr-strs)
				instr-strs)))
		lab-blks)
	  "\n\n")))

