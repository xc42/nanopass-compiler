(let ([x 2])
  (let ([arr (make-vector (* x x) (* x 3))])
	(let ([y (- (* x x) 1)])
	  (begin 
		(vector-set! arr y -6)
		(vector-set! arr 0 -7)
		(+ (vector-length arr)
		   (+ (vector-ref arr y) (vector-ref arr 0)))))))
