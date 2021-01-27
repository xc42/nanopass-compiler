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
  (letrec ([is-atom?
             (lambda (expr)
               (match expr
                      [(Int n) #t]
                      [(Var v) #t]
                      [other #f]))]
           [rco-atom
             (lambda (expr)
               (let ([cur (gensym 'tmp)])
                 (let ([rco-sub-recur
                         (lambda (subexp)
                           (if (is-atom? subexp)
                               (values subexp '())
                               (rco-atom subexp)))])
                   (match expr
                          [(Prim '- (list e)) 
                           (let-values ([(tmpvar alist) (rco-sub-recur e)])
                             (values cur (cons (cons cur (Prim '- (list tmpvar))) alist)))]
                          [(Prim '+ (list e1 e2))
                           (let-values ([(tmpvar1 alist1) (rco-sub-recur e1)]
                                        [(tmpvar2 alist2) (rco-sub-recur e2)])
                             (values cur (cons (cons cur (Prim '+ (list tmpvar1 tmpvar2))) (append alist1 alist2))))]
                          [(Let var expr body)
                           (values cur (list (cons cur (Let var (rco-expr expr) (rco-expr body)))))]
                          [other (values cur (list (cons cur expr)))]))))]

                             
           [rco-expr
             (lambda (expr)
               (letrec ([build-acc
                          (lambda (start alist)
                            (let ([val-exp (cdr (assoc start alist))])
                              (letrec ([build-acc-recur
                                         (lambda (body)
                                           (let ([build-Let
                                                   (lambda (tmpvar expr)
                                                     (if (symbol? tmpvar)
                                                         (build-acc-recur (Let tmpvar (cdr (assoc tmpvar alist)) expr))
                                                         expr))])

                                             (match body
                                                    [(Int n) body]
                                                    [(Var n) body]
                                                    [(Prim '- (list tmpvar)) (build-Let tmpvar)]
                                                    [(Prim '+ (list tmpvar1 tmpvar2)) 
                                                     (build-Let tmpvar2 (build-Let tmpvar1 body))]
                                                    [(Let v e body)
                                                     (Let v (build-acc-recur e) (build-acc-recur body))])))])
                                (build-acc-recur val-exp))))])

               (match expr
                      [(Int n) expr]
                      [(Var v) expr]
                      [(Prim '- e1)
                       (let-values ([(cur alist) (rco-atom expr)])
                         (build-acc  cur alist))]
                      [(Prim '+ es)
                       (let-values ([(cur alist) (rco-atom expr)])
                         (build-acc  cur alist))]
                      [(Let var e body) (Let var (rco-expr e) (rco-expr body))])))])
    (match p
           [(Program info e) (Program info (rco-expr e))])))
                       



;; explicate-control : R1 -> C0
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; print-x86 : x86 -> string
(define (print-x86 p)
  (error "TODO: code goes here (print-x86)"))
