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

(define (add8 [y0 : Integer]
			  [y1 : Integer]
			  [y2 : Integer]
			  [y3 : Integer]
			  [y4 : Integer]
			  [y5 : Integer]
			  [y6 : Integer]
			  [y7 : Integer]) : Integer
  (+ y0 (+ y1 (+ y2 (+ y3 (+ y4 (+ y5 (+ y6 (+ y7)))))))))

((partial add8 8) 7 6 5 4 3 2 1)
