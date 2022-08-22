(let ([x 2])
  (let ([arr (make-vector (* x x) (* x 3))])
	(let ([y (- (* x x) 1)])
	  (begin 
		(vector-set! arr y x)
		(vector-set! arr x y)
		(+ (vector-length arr)
		   (+ (vector-ref arr y) (vector-ref arr x)))))))
