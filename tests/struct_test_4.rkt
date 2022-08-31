(struct pair ([flag : Boolean]
			  [val : Integer]) #:mutable)

(define (func [ps : (Vectorof pair)]) : Integer
  (let* ([i 0]
		[l (vector-length ps)]
		[acc 0])

	(while (< i l)
		   (if (pair-flag (vector-ref ps i))
			 (set! acc (+ acc (pair-val (vector-ref ps i))))
			 (void))
		   (set! i (+ i 1)))
	acc))


(let ([ps (make-vector 5 (pair #t 3))])
  (set-pair-flag! (vector-ref ps 4) #f)
  (func ps))

