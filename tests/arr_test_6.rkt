(let ([x 8])
  (let ([y x])
	(let ([z (+ x y)])
	  (let ([a (+ x (+ y z))])
		(+ (/ a (+ x y))
		   (* (/ x 2) (/ 4 y)))))))

