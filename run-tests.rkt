#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Rvar.rkt")
(require "interp-Rif.rkt")
(require "type-check-Rif.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
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
	;("patch instructions",patch-instructions ,interp-x86-1) 
	))

(interp-tests "r2" type-check-Rif r2-passes interp-Rif "r2_test" (tests-for "r2"))
