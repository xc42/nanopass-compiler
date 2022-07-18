(define (partial [f : (Integer Integer Integer Integer Integer Integer Integer Integer  -> Integer)]
				 [x : Integer]) : (Integer Integer Integer Integer Integer Integer Integer  -> Integer)
  (lambda: ([x1 : Integer]
			[x2 : Integer]
			[x3 : Integer]
			[x4 : Integer]
			[x5 : Integer]
			[x6 : Integer]
			[x7 : Integer]) : Integer
		   (f x x1 x2 x3 x4 x5 x6 x7)))

(define (add8 [x0 : Integer]
			  [x1 : Integer]
			  [x2 : Integer]
			  [x3 : Integer]
			  [x4 : Integer]
			  [x5 : Integer]
			  [x6 : Integer]
			  [x7 : Integer]) : Integer
  (+ x0 (+ x1 (+ x2 (+ x3 (+ x4 (+ x5 (+ x6 (+ x7)))))))))

((partial add8 8) 7 6 5 4 3 2 1)
