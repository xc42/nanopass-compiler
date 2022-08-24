(define (bsearchRecur [arr : (Vectorof Integer)] 
					  [low : Integer]
					  [high : Integer]
					  [target : Integer]) : Boolean
  (if (>= low high)
	(eq? (vector-ref arr low) target)
	(let ([i (/ (+ low high) 2)])
	  (let ([mid (vector-ref arr i)])
		  (if (eq? target mid)
			#t
			(if (< target mid)
			  (bsearchRecur arr low i target)
			  (bsearchRecur arr i high target)))))))


(define (bsearch [arr : (Vectorof Integer)]
				 [target : Integer]) : Boolean
  (bsearchRecur arr 0 (vector-length arr) target))


(let ([arr (make-vector 10 100)])
  (begin
	(vector-set! arr 0 1)
	(vector-set! arr 9 101)
  (if (and (and (bsearch arr 100) (bsearch arr 1))
		   (and (bsearch arr 101) (not (bsearch arr -1))))
	23
	12)))
		   
