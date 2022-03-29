(let ([x (vector 1 2)])
  (let ([y (vector 3 4)])
	(let ([_ (vector-set! x 1 y)])
	  (if (= 3 (vector-ref (vector-ref x 1) 0))
		  (let ([_ (vector-set! y 1 x)])
			(if (= 1 (vector-ref (vector-ref (vector-ref (vector-ref y 1) 1) 1) 0))
				42
				43))
		  44))))
