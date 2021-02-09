#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rint.rkt")
(require "utilities.rkt")
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
                       [(Let v e body) (build-from-branches v (build-from-branches body expr0))]))])
                build-from-branches))])

      (match expr
        [(Int n) expr]
        [(Var n) expr]
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
		 [(Int n) '(,(Instr 'movq (list (Imm n) dst)))]
		 [(Var v) '(,(Instr 'movq (list (Var v) dst)))]
		 [(Prim '- `(,e)) '(,(Instr 'negq (list e)))]
		 [(Prim '+ `(,e1 ,e2))
		  (cond
			[(and (Int? e1) (Int? e2)) 
			 (match-let ([(Int n1) e1] [(Int n2) e2]) '(,(Instr 'movq (list (Imm (+ n1 n2)) (Var v)))))] 
			[(or (Int? e1) (Int? e2))
			 (match-let ([(Int n) (if (Int? e1) e1 e2)] [(Var v) (if (Int? e2) e1 e2)] [(Var var) dst]) 
			   (if (eq? v var) 
				 '(,(Instr 'addq (list (Imm n) dst)))
				 '(,(Instr 'movq (list (Imm n) dst)) ,(Inst 'addq (list (Var v) dst)))))]
			[else 
			  (match-let ([(Var v1) e1] [(Var v2) e2] [(Var var) dst])
				(cond
				  [(eq? v1 var) '(,(Instr 'addq (list e2 dst)))]
				  [(eq? v2 var) '(,(Instr 'addq (list e1 dst)))]
				  [else '(,(Instr 'movq (list e1 dst)) ,(Instr 'addq (list e2 dst)))]))])])))

  (match p
	[(CProgram info (list (label . stmts) ...))


;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; print-x86 : x86 -> string
(define (print-x86 p)
  (error "TODO: code goes here (print-x86)"))
