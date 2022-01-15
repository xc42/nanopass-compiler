#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rint.rkt")
(require "utilities.rkt")
(require "type-check-Cvar.rkt")
(require graph)
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

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (lookup x env))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let ([x* (gensym x)])
         (Let x* ((uniquify-exp env) e) ((uniquify-exp (extend-env env x x*)) body)))]
	  [(Prim 'read '()) e]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (define (rco-atom expr)
    (let ([expr-sym (gensym 'tmp)])
      (match expr
        [(Prim '+ `(,e1 ,e2)) 
         (if (atm? e1)
           (if (atm? e2)
             (values expr-sym `((,expr-sym . ,expr)))
             (values expr-sym 
                     (let-values ([(e2-sym e2-alist) (rco-atom e2)])
                       (cons (cons expr-sym  (Prim '+ `(,e1 ,(Var e2-sym)))) e2-alist))))
           (if (atm? e2)
             (values expr-sym 
                     (let-values ([(e1-sym e1-alist) (rco-atom e1)])
                       (cons (cons expr-sym  (Prim '+ `(,(Var e1-sym) ,e2))) e1-alist)))
             (values expr-sym
                     (let-values ([(e1-sym e1-alist) (rco-atom e1)]
                                  [(e2-sym e2-alist) (rco-atom e2)])
                       (cons (cons expr-sym (Prim '+ `(,(Var e1-sym) ,(Var e2-sym)))) (append e1-alist e2-alist))))))]
        [(Prim '- `(,e))
         (if (atm? e)
           (values expr-sym `((,expr-sym . ,expr)))
           (values expr-sym 
                   (let-values ([(e-sym e-alist) (rco-atom e)])
                     (cons (cons expr-sym  (Prim '- `(,(Var e-sym)))) e-alist))))]
        [(Let v e body) (values expr-sym (list (cons expr-sym (Let v (rco-expr e) (rco-expr body)))))])))

  (define (rco-expr expr)
    (let ([build 
            (lambda (alist)
              (letrec 
                ([build-from-branches
                   (lambda (tmp-expr expr0)
                     (match tmp-expr
                       [(Int n) expr0]
                       [(Var var) 
                        (let ([kv (assoc var alist)])
                          (if kv (build-from-branches (cdr kv) (Let var (cdr kv) expr0)) expr0))]
                       [(Prim '- `(,e)) (build-from-branches e expr0)]
                       [(Prim '+ `(,e1 ,e2)) (build-from-branches e1 (build-from-branches e2 expr0))]
                       [(Let v e body) (build-from-branches e (build-from-branches body expr0))]))])
                build-from-branches))])

      (match expr
        [(Int n) expr]
        [(Var n) expr]
		[(Prim 'read '()) expr]
        [_ (let-values ([(start-sym alist) (rco-atom expr)]) 
             (let ([tmp-expr (cdr (assoc start-sym alist))])
               (match tmp-expr
                 [(Prim '+ _) ((build alist) tmp-expr tmp-expr)]
                 [(Prim '- _) ((build alist) tmp-expr tmp-expr)]
                 [_ tmp-expr])))])))

  (match p
    [(Program info e) (Program info (rco-expr e))]))



;; explicate-control : R1 -> C0
(define (explicate-control p)
  (letrec
    ([explicate-assign
       (lambda (var expr acc)
         (match expr
           [(Let v e body)
            (explicate-assign v e (explicate-assign var body acc))]
           [other (cons (Assign (Var var) expr) acc)]))]
     [explicate-tail
       (lambda (expr)
         (match expr
           [(Let var e body)
            (foldr Seq (explicate-tail body) (explicate-assign var e '()))]
           [other (Return expr)]))])
  (match p
    [(Program info e)
     (CProgram info `((start . ,(explicate-tail e))))])))

       

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (define (trans-C0-assign stmt)
	(match-let ([(Assign dst expr) stmt])
	   (match expr
		 [(Int n) `(,(Instr 'movq (list (Imm n) dst)))]
		 [(Var v) `(,(Instr 'movq (list (Var v) dst)))]
		 [(Prim 'read '()) `(,(Callq 'read_int 0) ,(Instr 'movq (list (Reg 'rax) dst)))]
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
				 `(,(Instr 'movq (list (Imm n) dst)) ,(Instr 'addq (list (Var v) dst)))))]
			[else 
			  (match-let ([(Var v1) e1] [(Var v2) e2] [(Var var) dst])
				(cond
				  [(eq? v1 var) `(,(Instr 'addq (list e2 dst)))]
				  [(eq? v2 var) `(,(Instr 'addq (list e1 dst)))]
				  [else `(,(Instr 'movq (list e1 dst)) ,(Instr 'addq (list e2 dst)))]))])])))
  
  (define (trans-stmts stmts)
	(match stmts
	  [(Seq s1 tail) (append (trans-C0-assign s1) (trans-stmts tail))]
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
					   [(Prim '- `(,e))
						(if (Int? e)
						  (match-let ([(Int n) e]) `(,(Instr 'movq (list (Imm (- n)) (Reg 'rax)))))
						  `(,(Instr 'movq (list e (Reg 'rax))) ,(Instr 'negq (list (Reg 'rax)))))]
					   [(Int n) `(,(Instr 'movq (list (Imm n) (Reg 'rax))))]
					   [_ `(,(Instr 'movq (list expr (Reg 'rax))))])]))
  (match (type-check-Cvar p)
	[(CProgram info (list lab-sts ...))
	 (X86Program info
				 (map 
				   (lambda (ls)
					 (let ([label (car ls)] [stmts (cdr ls)])
					   (cons label (Block info (trans-stmts stmts)))))
				   lab-sts))]))


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
			  [(Instr 'movq (list (Deref reg1 offset1) (Deref reg2 offset2)))
			   `(,(Instr 'movq (list (Deref reg1 offset1) (Reg 'rax)))
				  ,(Instr 'movq (list (Reg 'rax) (Deref reg2 offset2))))]
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


;; print-x86 : x86 -> string
(define (print-x86 p)
  (define (print-instr instr)
	(let ([print-item
			(lambda (item)
			  (match item
				[(Reg r) (~a "%" r)]
				[(Imm n) (~a "$" n)]
				[(Deref r o) (format "~a(%~a)" o r)]))])
	(match instr
	  [(Instr op args) (format "~a ~a" op (string-join (map print-item args) " "))]
	  [(Callq func _) (~a "callq" func)])))

  (match-let* ([(X86Program info lab-blks) p]
			   [(Block info instrs) (cdr (assoc 'start lab-blks))]
			   [stack-size (* (length (assoc 'locals-types info)) 8)])
	(string-append
	  "start:\n\t"
	  (string-join (map print-instr instrs) "\n\t")
	  "\n\tjump conclusion\n\n\t"
	  ".globl main\n"
	  "main:\n\t"
	  "push %rbp\n\t"
	  "movq %rsp %rbp\n\t"
	  (format "subq $~a %rsp\n\t" stack-size)
	  "jump start\n\n"
	  "conclusion:\n\t"
	  (format "addq $~a %rsp\n\t" stack-size)
	  "popq %rbx\n\t"
	  "ret")))

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

(define (uncover-live p)
  (match-letrec ([(X86Program info lab-blks) p]
			   [lab-live-map (make-hash '())] ;;memorize
			   [uncover-one-instr
				 (lambda (instr live-after)
				   (match instr
						  [(Instr (or 'addq 'subq) `(,arg1 ,arg2)) 
						   (if (Imm? arg1) 
							   (set-add live-after arg2) 
							   (set-union live-after (set arg1 arg2)))]
						  [(Instr 'movq `(,arg1 ,arg2)) 
						   (if (Imm? arg1) 
							   (set-remove live-after arg2)
							   (set-add (set-remove live-after arg2) arg1))]
						  [(Instr 'negq `(,e)) (set-add live-after e)]
						  [(Instr 'jmp `(,label)) (car (uncover-lab-blk (assoc label lab-blks)))]
						  [(Callq label _) (set-remove live-after (apply set (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11))))] ;;TODO
						  [(Retq) live-after] ;;TODO
						  ))]
			  [uncover-block	(lambda (stmts) 
								  (foldr (lambda (instr acc-live-set) (cons (uncover-one-instr instr (car acc-live-set)) acc-live-set))
										 `(,(set))
										 stmts))]
			  [uncover-lab-blk (lambda (lab-blk)
								 (let ([lab (car lab-blk)] [blk (cdr lab-blk)])
								   (if (hash-has-key? lab-live-map lab)
									   (hash-ref lab-live-map lab)
									   (match-let* ([(Block info stmts) blk]
												   [live-set (uncover-block stmts)])
												   (begin 
													 (hash-set! lab-live-map lab live-set) ;;remember this label's live set
													 live-set)))))])
			  (X86Program info 
						  (map 
							(lambda (lab-blk) 
							  (match-let ([(cons label (Block info stmts)) lab-blk])
										 (cons label (Block (cons 'live-set (uncover-lab-blk lab-blk)) stmts))))
							lab-blks))))

(define (build-interference p)
  (let ([graph-from 
		  (lambda (live-sets instrs)
			(foldl
			  (lambda (instr-lives g)
				(match-let* 
				  ([(cons instr lives) instr-lives]
				   [(cons rs ws) (get-instr-RW-set instr)])
				  1; //TODO
				  ))
			  (undirected-graph '())
			  (map cons instrs (cdr live-sets))))])
  (match-let* ([(X86Program info lab-blks) p]
			  [(cons 'start (Block binfo stmts)) (assoc 'start lab-blks)]
			  [(cons 'live-set live-sets) (assoc 'live-set binfo)])
			  
			  (X86Program (cons (cons 'conflicts (graph-from live-sets stmts) info)) lab-blks))))
