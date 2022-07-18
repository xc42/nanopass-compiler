#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Rvar.rkt")
(require "interp-Rif.rkt")
(require "type-check-Rlambda.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
(require "interp-Cvec.rkt")
(require "interp-Cfun.rkt")
(require "interp-Rvec.rkt")
(require "interp-Rvec-prime.rkt")
(require "interp-Rfun.rkt")
(require "interp-Rfun-prime.rkt")
(require "interp-Rlambda.rkt")


(require "interp.rkt")
(require "compiler.rkt")
;; (debug-level 1)
;; (AST-output-syntax 'concrete-syntax)

;; Define the passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; should be named "compiler.rkt"
(define passes
  `( ("uniquify" ,uniquify ,interp-Rvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Rvar)
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
          (string=? r (car (string-split p "_"))))
        all-tests)))

;(interp-tests "var" #f passes interp-Rvar "var_test" (tests-for "var"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;(compiler-tests "var" #f passes "var_test" (tests-for "var"))


(define r2-passes
  `(("shrink" ,shrink ,interp-Rif)
	("uniquify" ,uniquify ,interp-Rif)
	("remove complex opera*" ,remove-complex-opera* ,interp-Rif)
	("explicate control" ,explicate-control ,interp-Cif)
	("instruction selection" ,select-instructions ,interp-x86-1)
	("remove jumps" ,remove-jumps ,interp-x86-1)
	("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-x86-1)
	("patch instructions",patch-instructions ,interp-x86-1) 
	("print x86" ,print-x86 #f)
	))

;(interp-tests "r2" type-check-Rif r2-passes interp-Rif "r2_test" (tests-for "r2"))
;(compiler-tests "r2" type-check-Rif r2-passes "r2_test" (tests-for "r2"))

(define r3-passes
  `(("shrink" ,shrink ,interp-Rvec)
	("uniquify" ,uniquify ,interp-Rvec)
	("expose allocation" ,expose-allocation ,interp-Rvec-prime)
	("remove complex opera*" ,remove-complex-opera* ,interp-Rvec-prime)
	("explicate control" ,explicate-control ,interp-Cvec)
	("instruction selection" ,select-instructions ,interp-x86-2)
	("remove jumps" ,remove-jumps ,interp-x86-2)
	("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-x86-2)
	("patch instructions",patch-instructions ,interp-x86-2) 
	("print x86" ,print-x86 #f)
	))

;(interp-tests "r3" type-check-Rvec r3-passes interp-Rvec "r3_test" (tests-for "r3"))
;(compiler-tests "r3" type-check-Rvec r3-passes "r3_test" (tests-for "r3"))

(define r4-passes
  `(("shrink" ,shrink ,interp-Rfun)
	("uniquify" ,uniquify ,interp-Rfun-prime)
	("reaveal functions" ,reveal-functions ,interp-Rfun-prime)
	("limit functions" ,limit-functions ,interp-Rfun-prime)
	("expose allocation" ,expose-allocation ,interp-Rfun-prime)
	("remove complex opera*" ,remove-complex-opera* ,interp-Rfun-prime)
	("explicate control" ,explicate-control ,interp-Cfun)
	("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
	("remove jumps" ,remove-jumps ,interp-pseudo-x86-3)
	("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-pseudo-x86-3)
	("patch instructions",patch-instructions ,interp-x86-3) 
	("print x86" ,print-x86 #f)
	))
;(interp-tests "r4" type-check-Rfun r4-passes interp-Rfun "r4_test" (tests-for "r4"))
;(compiler-tests "r4" type-check-Rfun r4-passes "r4_test" (tests-for "r4"))



(define r5-passes
  `(("shrink" ,shrink ,interp-F2)
	("uniquify" ,uniquify ,interp-F2)
	("reaveal functions" ,reveal-functions ,interp-F2)
	("closure conversion" ,convert-to-closure ,interp-F2)
	;("limit functions" ,limit-functions ,interp-F2)
	;("expose allocation" ,expose-allocation ,interp-Rlambda-prime)
	;("remove complex opera*" ,remove-complex-opera* ,interp-Rlambda-prime)
	;("explicate control" ,explicate-control ,interp-Cfun)
	;("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
	;("remove jumps" ,remove-jumps ,interp-pseudo-x86-3)
	;("allocate register" ,(lambda (p) (allocate-register (build-interference (uncover-live p)))) ,interp-pseudo-x86-3)
	;("patch instructions",patch-instructions ,interp-x86-3) 
	;("print x86" ,print-x86 #f)
	))
(interp-tests "r5" type-check-Rlambda r5-passes interp-Rlambda "r5_test" (tests-for "r5"))
;(compiler-tests "r5" type-check-Rlambda r5-passes "r5_test" (tests-for "r5"))
