#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "type-check-Llambda.rkt")
(require "interp-Llambda.rkt")
(require "interp-Llambda-prime.rkt")
(require "interp-Clambda.rkt")
(require "interp.rkt")
(require "compiler.rkt")
;; (debug-level 1)
;; (AST-output-syntax 'concrete-syntax)

;; Define the passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; should be named "compiler.rkt"
#;(define passes
  `( ("uniquify" ,uniquify ,interp-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-x86-0)
     ;("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("print x86" ,print-x86 #f)
     ))

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          ;(string=? r (car (string-split p "_"))))
		  (string-prefix? p r))
        all-tests)))

;(interp-tests "var" #f passes interp-Lvar "var_test" (tests-for "var"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;(compiler-tests "var" #f passes "var_test" (tests-for "var"))


#;(define r2-passes
  `(("shrink" ,shrink ,interp-Lif)
	("uniquify" ,uniquify ,interp-Lif)
	("remove complex opera*" ,remove-complex-opera* ,interp-Lif)
	("explicate control" ,explicate-control ,interp-Cif)
	("instruction selection" ,select-instructions ,interp-x86-1)
	("remove jumps" ,remove-jumps ,interp-x86-1)
	("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-x86-1)
	("patch instructions",patch-instructions ,interp-x86-1) 
	("print x86" ,print-x86 #f)
	))

;(interp-tests "r2" type-check-Rif r2-passes interp-Lif "r2_test" (tests-for "r2"))
;(compiler-tests "r2" type-check-Rif r2-passes "r2_test" (tests-for "r2"))

#;(define r3-passes
  `(("shrink" ,shrink ,interp-Lvec)
	("uniquify" ,uniquify ,interp-Lvec)
	("expose allocation" ,expose-allocation ,interp-Lvec-prime)
	("remove complex opera*" ,remove-complex-opera* ,interp-Lvec-prime)
	("explicate control" ,explicate-control ,interp-Cvec)
	("instruction selection" ,select-instructions ,interp-x86-2)
	("remove jumps" ,remove-jumps ,interp-x86-2)
	("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-x86-2)
	("patch instructions",patch-instructions ,interp-x86-2) 
	("print x86" ,print-x86 #f)
	))

;(interp-tests "r3" type-check-Rvec r3-passes interp-Lvec "r3_test" (tests-for "r3"))
;(compiler-tests "r3" type-check-Rvec r3-passes "r3_test" (tests-for "r3"))

#;(define r4-passes
  `(("shrink" ,shrink ,interp-Lfun)
	("uniquify" ,uniquify ,interp-Lfun-prime)
	("reaveal functions" ,reveal-functions ,interp-Lfun-prime)
	("limit functions" ,limit-functions ,interp-Lfun-prime)
	("expose allocation" ,expose-allocation ,interp-Lfun-prime)
	("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime)
	("explicate control" ,explicate-control ,interp-Cfun)
	("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
	("remove jumps" ,remove-jumps ,interp-pseudo-x86-3)
	("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-pseudo-x86-3)
	("patch instructions",patch-instructions ,interp-x86-3) 
	("print x86" ,print-x86 #f)
	))
;(interp-tests "r4" type-check-Rfun r4-passes interp-Lfun "r4_test" (tests-for "r4"))
;(compiler-tests "r4" type-check-Rfun r4-passes "r4_test" (tests-for "r4"))



#;(define r5-passes
  `(("shrink" ,shrink ,interp-F2)
	("uniquify" ,uniquify ,interp-F2)
	("reaveal functions" ,reveal-functions ,interp-F2)
	("closure conversion" ,convert-to-closure ,interp-F2) 
	;("limit functions" ,limit-functions ,interp-F2) ;; too nasty to write transform at both def & call site and type consistency of func type & closure type (considering a more graceful and efficient argument passing maner later...)
	("expose allocation" ,expose-allocation ,interp-F2)
	("remove complex opera*" ,remove-complex-opera* ,interp-F2)
	("explicate control" ,explicate-control ,interp-Clambda)
	("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
	("remove jumps" ,remove-jumps ,interp-pseudo-x86-3)
	("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-pseudo-x86-3)
	("patch instructions",patch-instructions ,interp-x86-3) 
	("print x86" ,print-x86 #f)
	))
;(interp-tests "r5" type-check-Llambda r5-passes interp-Llambda "r5_test" (tests-for "r5"))
;(compiler-tests "r5" type-check-Llambda r5-passes "r5_test" (tests-for "r5"))

(define r8-passes
  `(("shrink" ,shrink ,interp-Llambda)
	("uniquify" ,uniquify ,interp-Llambda)
	("reaveal functions" ,reveal-functions ,interp-Llambda-prime)
	("convert assignment" ,convert-assignment ,interp-Llambda-prime)
	("closure conversion" ,convert-to-closure ,interp-Llambda-prime) 
	;;;("limit functions" ,limit-functions ,interp-F2) ;; too nasty to write transform at both def & call site and type consistency of func type & closure type (considering a more graceful and efficient argument passing maner later...)
	("expose allocation" ,expose-allocation ,interp-Llambda-prime)
	("remove complex opera*" ,remove-complex-opera* ,interp-Llambda-prime)
	("explicate control" ,explicate-control ,interp-Clambda)
	("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
	("remove jumps" ,remove-jumps ,interp-pseudo-x86-3)
	("uncovert liveness" ,uncover-live ,interp-pseudo-x86-3)
	("build interference graph" ,build-interference ,interp-pseudo-x86-3)
	("allocate register" ,allocate-register ,interp-pseudo-x86-3)
	("patch instructions",patch-instructions ,interp-x86-3) 
	("print x86" ,print-x86 #f)
	))
;(interp-tests "r8" type-check-Llambda r8-passes interp-Llambda "r8_test" (tests-for "r8"))
;(compiler-tests "r8" type-check-Llambda r8-passes "r8_test" (tests-for "r8"))
(interp-tests "arr" type-check-Llambda r8-passes interp-Llambda "arr_test" (tests-for "arr_test"))
(compiler-tests "arr" type-check-Llambda r8-passes "arr_test" (tests-for "arr"))
