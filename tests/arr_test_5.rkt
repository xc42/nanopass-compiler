(define (sum [arr : (Vectorof Integer)]) : Integer
  (let ([i 0])
	(let ([len (vector-length arr)])
	  (let ([sum 0])
		(begin
		  (while (< i len)
				 (begin
				   (set! sum (+ sum (vector-ref arr i)))
				   (set! i (+ i 1))))
		  sum)))))

(let ([arr (make-vector 100 0)])
  (let ([i 1])
	(begin 
	  (while (<= i 100)
			 (begin
			   (vector-set! arr (- i 1) i)
			   (set! i (+ i 1))))
	  (- (sum arr) 5050))))
	

